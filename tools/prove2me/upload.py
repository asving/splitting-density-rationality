#!/usr/bin/env python3
"""Upload the prepared TypeDensity bundle to Prove2Me, one node at a time, in ORDER.json order.

Standard library only. Written against the platform documentation version 0.13.9
(https://prove2.me/skill.md and https://prove2.me/references/). ORDER is the order file that
build_bundle.py wrote into the work directory (WORK/ORDER.json, or
WORK/ORDER.padicint-as-module.json for the alternative ordering).

    python3 upload.py --order ORDER --dry-run             print every request it would make; no network, no key
    python3 upload.py --order ORDER --dry-run --verbose   the same, with full request bodies
    python3 upload.py --order ORDER                       upload; resumes from the state file if interrupted
    python3 upload.py --order ORDER --only NAME           only the entries with that name

What it does for each entry of the order file:

    definition  POST /submit-definition   (JSON body = the payload file, byte for byte)
                poll GET /publish-jobs/<job_id> until PUBLISHED | FAILED | ERROR
    problem     POST /submit-problem      (JSON body = the payload file, byte for byte)
                poll GET /publish-jobs/<job_id>; keep the job's theorem_id
    solution    POST /verify              (multipart: theorem_id, proof_type=prove, file)
                poll GET /verify?submission_id=<id> until it is no longer PENDING

Before each POST it writes the intent to the state file, and after the POST it writes the returned
job_id or submission_id before it starts polling. A rerun therefore polls what was already
submitted instead of submitting again. It stops at the first failure and prints the platform's
error message.

The API key is read from ~/.config/prove2me/api_key and exchanged at POST /agent/refresh for a
one-hour access token. Key and token are sent to https://prove2.me/api/v1/ only: every request goes
through one function that refuses any other URL, and redirects are not followed.
"""
import argparse
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

API_SCHEME = "https"
API_HOST = "prove2.me"
API_PREFIX = "/api/v1"
API_BASE = "%s://%s%s" % (API_SCHEME, API_HOST, API_PREFIX)
DOCS_VERSION = "0.13.9"
KEY_FILE = os.path.join("~", ".config", "prove2me", "api_key")
USER_AGENT = "typedensity-bundle-uploader/1"

JOB_OK = "PUBLISHED"
JOB_FINAL = {"PUBLISHED", "FAILED", "ERROR"}
SUB_OK = "ACCEPTED"
SUB_FINAL = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}


class Stop(Exception):
    """A condition that ends the run; the message is shown to the operator."""


# ---------------------------------------------------------------------------------------------
# HTTP: the only place a request is made
# ---------------------------------------------------------------------------------------------

class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None  # a redirect becomes an HTTPError; credentials are never forwarded


def check_url(url):
    """Refuse anything that is not https://prove2.me/api/v1/..."""
    u = urllib.parse.urlsplit(url)
    ok = (u.scheme == API_SCHEME and u.hostname == API_HOST and u.port in (None, 443)
          and u.username is None and u.password is None
          and (u.path == API_PREFIX or u.path.startswith(API_PREFIX + "/")))
    if not ok:
        raise Stop("refusing to send a request to %r: only %s is allowed" % (url, API_BASE))
    return url


class Transport:
    """Real network transport. request() returns (status, body_bytes)."""

    def __init__(self):
        self._opener = urllib.request.build_opener(_NoRedirect())

    def request(self, method, url, headers, body, timeout):
        check_url(url)
        req = urllib.request.Request(url, data=body, method=method)
        for k, v in headers.items():
            req.add_header(k, v)
        try:
            with self._opener.open(req, timeout=timeout) as resp:
                return resp.getcode(), resp.read()
        except urllib.error.HTTPError as e:
            return e.code, e.read()


def multipart(fields, file_field, filename, file_bytes):
    boundary = "----typedensity" + uuid.uuid4().hex
    parts = []
    for k, v in fields:
        parts.append(("--%s\r\nContent-Disposition: form-data; name=\"%s\"\r\n\r\n%s\r\n" % (boundary, k, v)).encode("utf-8"))
    parts.append(("--%s\r\nContent-Disposition: form-data; name=\"%s\"; filename=\"%s\"\r\n"
                  "Content-Type: application/octet-stream\r\n\r\n" % (boundary, file_field, filename)).encode("utf-8"))
    parts.append(file_bytes)
    parts.append(("\r\n--%s--\r\n" % boundary).encode("utf-8"))
    return b"".join(parts), "multipart/form-data; boundary=" + boundary


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def message_of(body):
    """The human-readable part of an error response."""
    try:
        obj = json.loads(body.decode("utf-8"))
    except Exception:
        return body.decode("utf-8", "replace")[:2000]
    if isinstance(obj, dict):
        for k in ("error_message", "error", "message", "detail"):
            if obj.get(k):
                return str(obj[k])
        if obj.get("errors"):
            return json.dumps(obj["errors"], ensure_ascii=False)
    return json.dumps(obj, ensure_ascii=False)[:2000]


# ---------------------------------------------------------------------------------------------
# Order file and payloads
# ---------------------------------------------------------------------------------------------

def load_order(path):
    with open(path, encoding="utf-8") as f:
        order = json.load(f)
    base = os.path.dirname(os.path.abspath(path))
    entries = []
    for e in order["nodes"]:
        if e["kind"] not in ("definition", "problem", "solution"):
            raise Stop("unknown kind %r in %s" % (e["kind"], path))
        e = dict(e)
        e["payload_path"] = os.path.join(base, e["payload"])
        e["lean_path"] = os.path.join(base, e["lean"])
        e["key"] = "%s:%s" % (e["kind"], e["name"])
        entries.append(e)
    keys = [e["key"] for e in entries]
    if len(set(keys)) != len(keys):
        raise Stop("duplicate entries in %s" % path)
    return order, entries


def read_bytes(path):
    with open(path, "rb") as f:
        return f.read()


def prepare(entry):
    """Read and sanity-check what will be sent for an entry. No network."""
    raw = read_bytes(entry["payload_path"])
    payload = json.loads(raw.decode("utf-8"))
    lean = read_bytes(entry["lean_path"])
    if entry["kind"] == "definition":
        if payload.get("definition_name") != entry["name"]:
            raise Stop("%s: definition_name does not match the order file" % entry["payload"])
        if payload["definition"].encode("utf-8") != lean:
            raise Stop("%s: definition text differs from %s" % (entry["payload"], entry["lean"]))
        return dict(body=raw, payload=payload, lean=lean)
    if entry["kind"] == "problem":
        probs = payload.get("problems")
        if not isinstance(probs, list) or len(probs) != 1 or probs[0].get("theorem_name") != entry["name"]:
            raise Stop("%s: expected exactly one problem named %s" % (entry["payload"], entry["name"]))
        p = probs[0]
        if not p["formal_statement"].endswith(":= by sorry"):
            raise Stop("%s: formal_statement does not end with ':= by sorry'" % entry["payload"])
        if (p["preamble"] + "\n" + p["formal_statement"] + "\n").encode("utf-8") != lean:
            raise Stop("%s: preamble + statement differ from %s" % (entry["payload"], entry["lean"]))
        return dict(body=raw, payload=payload, lean=lean)
    if payload.get("theorem_name") != entry["name"]:
        raise Stop("%s: theorem_name does not match the order file" % entry["payload"])
    if payload.get("file_sha256") != sha256(lean):
        raise Stop("%s: file_sha256 does not match %s" % (entry["payload"], entry["lean"]))
    text = lean.decode("utf-8")
    if re.search(r"(?<![\w.])sorry(?![\w'])", text):
        raise Stop("%s contains sorry" % entry["lean"])
    if "import Theorems.Thm_%s\n" % entry["name"].replace(".", "_") in text:
        raise Stop("%s imports its own target" % entry["lean"])
    if not re.search(r"^theorem solution\b", text, flags=re.M):
        raise Stop("%s has no top-level `theorem solution`" % entry["lean"])
    return dict(body=None, payload=payload, lean=lean)


# ---------------------------------------------------------------------------------------------
# State
# ---------------------------------------------------------------------------------------------

class State:
    def __init__(self, path, variant):
        self.path = path
        self.data = {"format": 1, "variant": variant, "entries": {}}
        if os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                self.data = json.load(f)
            if self.data.get("variant") != variant:
                raise Stop("state file %s belongs to variant %r, the order file is %r; use another --state"
                           % (path, self.data.get("variant"), variant))

    def get(self, key):
        return self.data["entries"].get(key, {})

    def update(self, key, **kw):
        e = self.data["entries"].setdefault(key, {})
        e.update(kw)
        e["updated_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        self.save()

    def save(self):
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(self.data, f, indent=1, ensure_ascii=False)
            f.write("\n")
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, self.path)


# ---------------------------------------------------------------------------------------------
# Uploader
# ---------------------------------------------------------------------------------------------

class Uploader:
    def __init__(self, entries, state, transport, read_key, out=print, sleep=time.sleep, now=time.time,
                 poll_interval=5.0, poll_timeout=3600.0, accept_version=None):
        self.entries = entries
        self.state = state
        self.transport = transport
        self.read_key = read_key
        self.out = out
        self.sleep = sleep
        self.now = now
        self.poll_interval = poll_interval
        self.poll_timeout = poll_timeout
        self.accept_version = accept_version
        self._token = None
        self._token_exp = 0.0

    # -- authentication ----------------------------------------------------------------------
    def token(self, force=False):
        if not force and self._token and self.now() < self._token_exp - 300:
            return self._token
        key = self.read_key()
        status, body = self.transport.request(
            "POST", check_url(API_BASE + "/agent/refresh"),
            {"Content-Type": "application/json", "User-Agent": USER_AGENT},
            json.dumps({"api_key": key}).encode("utf-8"), 60)
        if status == 401:
            raise Stop("the API key was rejected (401): it has expired or been invalidated; "
                       "put a fresh key in %s" % KEY_FILE)
        if status != 200:
            raise Stop("token exchange failed with HTTP %d: %s" % (status, message_of(body)))
        obj = json.loads(body.decode("utf-8"))
        version = obj.get("version")
        if version and version != DOCS_VERSION and version != self.accept_version:
            raise Stop("the platform reports version %s; this script was written against the documentation "
                       "version %s. Re-read https://prove2.me/skill.md for changed endpoints, then rerun with "
                       "--platform-version %s" % (version, DOCS_VERSION, version))
        self._token = obj["access_token"]
        self._token_exp = float(obj.get("expires_at") or (self.now() + 3000))
        return self._token

    def call(self, method, path, body=None, content_type=None, query=None, idempotent=True):
        """One API call with the access token. Returns (status, parsed JSON or None, raw body).

        GET requests are retried on network errors, 5xx and 429. A POST is retried only on 401
        (after a token refresh) and 429, where the platform did not accept the request; any other
        doubt about a POST is raised as Ambiguous."""
        url = API_BASE + path
        if query:
            url += "?" + urllib.parse.urlencode(query)
        attempt = 0
        refreshed = False
        while True:
            attempt += 1
            headers = {"Authorization": "Bearer " + self.token(), "User-Agent": USER_AGENT,
                       "Accept": "application/json"}
            if content_type:
                headers["Content-Type"] = content_type
            try:
                status, raw = self.transport.request(method, check_url(url), headers, body, 120)
            except Stop:
                raise
            except Exception as e:  # network error, timeout
                if idempotent and attempt < 8:
                    self.sleep(min(60, 5 * attempt))
                    continue
                raise Ambiguous("network error on %s %s: %s" % (method, path, e))
            if status == 401 and not refreshed:
                refreshed = True
                self.token(force=True)
                continue
            if status == 429 and attempt < 20:
                self.out("    429 from the platform (too many queued jobs or requests); waiting 30 s")
                self.sleep(30)
                continue
            if status >= 500:
                if idempotent and attempt < 8:
                    self.sleep(min(60, 5 * attempt))
                    continue
                if not idempotent:
                    raise Ambiguous("HTTP %d on %s %s: %s" % (status, method, path, message_of(raw)))
            try:
                obj = json.loads(raw.decode("utf-8")) if raw else None
            except Exception:
                obj = None
            return status, obj, raw

    # -- one entry ---------------------------------------------------------------------------
    def run(self, only=None):
        todo = [e for e in self.entries if only is None or e["name"] == only]
        if only is not None and not todo:
            raise Stop("no entry named %r in the order file" % only)
        total = len(self.entries)
        for e in todo:      # read every payload before anything is sent
            prepare(e)
        if any(self.state.get(e["key"]).get("status") != "done" for e in todo):
            self.token()    # fail here, before any state is written, if the key is missing or rejected
        for e in todo:
            st = self.state.get(e["key"])
            label = "[%2d/%d] %-10s %s" % (e["step"], total, e["kind"], e["name"])
            if st.get("status") == "done":
                self.out(label + "  already done")
                continue
            self.out(label)
            prepared = prepare(e)
            if e["kind"] == "solution":
                self.do_solution(e, prepared)
            else:
                self.do_publish(e, prepared)
        self.out("all requested entries are done")

    def do_publish(self, e, prepared):
        key = e["key"]
        st = self.state.get(key)
        job_id = st.get("job_id") if st.get("status") == "submitted" else None
        if st.get("status") == "submitting":
            job_id = self.find_job(e)
            if job_id:
                self.out("    an earlier run was interrupted after submitting; adopting job %s" % job_id)
                self.state.update(key, status="submitted", job_id=job_id)
        if not job_id:
            path = "/submit-definition" if e["kind"] == "definition" else "/submit-problem"
            self.state.update(key, status="submitting", payload_sha256=sha256(prepared["body"]),
                              job_id=None, theorem_id=None, error=None)
            status, obj, raw = self.call("POST", path, prepared["body"], "application/json", idempotent=False)
            if status not in (200, 201, 202) or not isinstance(obj, dict):
                self.state.update(key, status="failed", error="HTTP %d: %s" % (status, message_of(raw)))
                raise Stop("%s was rejected before queueing (HTTP %d): %s" % (e["name"], status, message_of(raw)))
            if e["kind"] == "definition":
                job_id = obj.get("job_id")
            else:
                jobs = [j for j in obj.get("jobs") or [] if j.get("name") == e["name"]]
                job_id = jobs[0].get("job_id") if jobs else None
            if not job_id:
                err = json.dumps(obj.get("errors"), ensure_ascii=False) if obj.get("errors") else message_of(raw)
                self.state.update(key, status="failed", error=err)
                raise Stop("%s was rejected before queueing: %s" % (e["name"], err))
            self.state.update(key, status="submitted", job_id=job_id)
            self.out("    queued as publish job %s" % job_id)
        job = self.poll(lambda: self.call("GET", "/publish-jobs/%s" % urllib.parse.quote(job_id, safe="")),
                        JOB_FINAL, "publish job %s" % job_id)
        status = job.get("status")
        if status != JOB_OK:
            self.state.update(key, status="failed", job_status=status, error=job.get("error_message"))
            hint = " (an infrastructure fault according to the documentation: rerun to resubmit unchanged)" \
                if status == "ERROR" else ""
            raise Stop("%s: publish job %s ended %s%s\n%s" % (e["name"], job_id, status, hint,
                                                               job.get("error_message") or "(no error message)"))
        ids = {k: job[k] for k in ("theorem_id", "definition_id") if job.get(k)}
        if e["kind"] == "problem" and not ids.get("theorem_id"):
            self.state.update(key, status="failed", job_status=status, error="PUBLISHED without theorem_id")
            raise Stop("%s: job %s is PUBLISHED but carries no theorem_id" % (e["name"], job_id))
        self.state.update(key, status="done", job_status=status, **ids)
        self.out("    PUBLISHED %s" % " ".join("%s=%s" % kv for kv in sorted(ids.items())))

    def do_solution(self, e, prepared):
        key = e["key"]
        prob = self.state.get("problem:" + e["name"])
        theorem_id = prob.get("theorem_id") if prob.get("status") == "done" else None
        if not theorem_id:
            raise Stop("%s: its problem is not published yet according to the state file" % e["name"])
        st = self.state.get(key)
        sub_id = st.get("submission_id") if st.get("status") == "submitted" else None
        if st.get("status") == "submitting":
            sub_id = self.find_submission(theorem_id, prepared["lean"])
            if sub_id:
                self.out("    an earlier run was interrupted after submitting; adopting submission %s" % sub_id)
                self.state.update(key, status="submitted", submission_id=sub_id)
        if not sub_id:
            body, ctype = multipart([("theorem_id", theorem_id), ("proof_type", "prove")],
                                    "file", "solution.lean", prepared["lean"])
            self.state.update(key, status="submitting", theorem_id=theorem_id,
                              file_sha256=sha256(prepared["lean"]), submission_id=None, error=None)
            status, obj, raw = self.call("POST", "/verify", body, ctype, idempotent=False)
            sub_id = obj.get("submission_id") if isinstance(obj, dict) else None
            if status not in (200, 201, 202) or not sub_id:
                self.state.update(key, status="failed", error="HTTP %d: %s" % (status, message_of(raw)))
                raise Stop("%s: the proof was not accepted for verification (HTTP %d): %s"
                           % (e["name"], status, message_of(raw)))
            self.state.update(key, status="submitted", submission_id=sub_id)
            self.out("    submitted as %s" % sub_id)
        sub = self.poll(lambda: self.call("GET", "/verify", query={"submission_id": sub_id}),
                        SUB_FINAL, "submission %s" % sub_id)
        status = sub.get("status")
        if status != SUB_OK:
            self.state.update(key, status="failed", verdict=status, error=sub.get("error_message"))
            hint = ""
            if status == "SKETCH_ACCEPTED":
                hint = " (the proof compiles but imports a theorem that is still Open; check the order)"
            raise Stop("%s: submission %s ended %s%s\n%s" % (e["name"], sub_id, status, hint,
                                                             sub.get("error_message") or "(no error message)"))
        self.state.update(key, status="done", verdict=status)
        self.out("    ACCEPTED")

    def poll(self, fetch, final, what):
        start = self.now()
        delay = self.poll_interval
        last = None
        while True:
            status, obj, raw = fetch()
            if status == 200 and isinstance(obj, dict):
                s = obj.get("status")
                if s != last:
                    self.out("    %s: %s" % (what, s))
                    last = s
                if s in final:
                    return obj
            elif status == 404:
                raise Stop("%s is unknown to the platform (404): %s" % (what, message_of(raw)))
            else:
                self.out("    polling %s: HTTP %d %s" % (what, status, message_of(raw)[:200]))
            if self.now() - start > self.poll_timeout:
                raise Stop("%s did not finish within %d s; its id is in the state file, rerun to keep polling"
                           % (what, self.poll_timeout))
            self.sleep(delay)
            delay = min(15.0, delay * 1.3)

    # -- recovery after an interrupted POST --------------------------------------------------------
    def find_job(self, e):
        """Look for a publish job of this name that an interrupted run may have created."""
        kind = "definition" if e["kind"] == "definition" else "problem"
        status, obj, raw = self.call("GET", "/publish-jobs", query={"kind": kind, "limit": 100})
        jobs = None
        if status == 200:
            if isinstance(obj, list):
                jobs = obj
            elif isinstance(obj, dict):
                for k in ("jobs", "publish_jobs", "items", "results", "data"):
                    if isinstance(obj.get(k), list):
                        jobs = obj[k]
                        break
        if jobs is None:
            raise Stop("%s: an earlier run stopped between submitting and recording the job id, and the list of "
                       "publish jobs could not be read (HTTP %d). Look the job up by hand "
                       "(GET /api/v1/publish-jobs?kind=%s), then rerun with --adopt %s=<job_id>, or with "
                       "--resubmit %s if there is none." % (e["name"], status, kind, e["key"], e["key"]))
        for j in jobs:  # newest first
            if not isinstance(j, dict):
                continue
            name = j.get("theorem_name") or j.get("definition_name") or j.get("name")
            if name == e["name"] and j.get("status") in ("PENDING", "COMPILING", "PUBLISHED"):
                return j.get("id") or j.get("job_id")
        return None

    def find_submission(self, theorem_id, lean):
        """Look for a submission with exactly this file that an interrupted run may have created."""
        status, obj, raw = self.call("GET", "/theorems/%s/submissions" % urllib.parse.quote(theorem_id, safe=""),
                                     query={"limit": 50})
        if status != 200 or not isinstance(obj, dict) or not isinstance(obj.get("submissions"), list):
            raise Stop("an earlier run stopped between submitting a proof and recording its id, and the "
                       "submissions of theorem %s could not be listed (HTTP %d). Check by hand, then rerun with "
                       "--adopt solution:<name>=<submission_id> or --resubmit solution:<name>." % (theorem_id, status))
        want = sha256(lean)
        for s in obj["submissions"]:
            sid = s.get("id")
            if not sid or s.get("status") not in ("PENDING", "ACCEPTED", "SKETCH_ACCEPTED"):
                continue
            st2, o2, _ = self.call("GET", "/submissions/%s/solution" % urllib.parse.quote(sid, safe=""))
            if st2 == 200 and isinstance(o2, dict) and isinstance(o2.get("content"), str) \
                    and sha256(o2["content"].encode("utf-8")) == want:
                return sid
        return None


class Ambiguous(Stop):
    """A POST may or may not have reached the platform."""


# ---------------------------------------------------------------------------------------------
# Dry run
# ---------------------------------------------------------------------------------------------

def dry_run(order, entries, state_path, only, verbose, out=print):
    state = {}
    if os.path.exists(state_path):
        with open(state_path, encoding="utf-8") as f:
            state = json.load(f).get("entries", {})
    out("DRY RUN: nothing is sent, the API key is not read.")
    out("order: variant %s, %d entries, environment %s" % (order.get("variant"), len(entries), order.get("env")))
    out("state file: %s (%s)" % (state_path, "exists" if state else "not present yet"))
    out("")
    out("first request of a real run:")
    out("  POST %s/agent/refresh   Content-Type: application/json" % API_BASE)
    out("  body: {\"api_key\": <contents of %s>}" % KEY_FILE)
    out("  every later request carries  Authorization: Bearer <access_token>")
    out("")
    todo = [e for e in entries if only is None or e["name"] == only]
    if only is not None and not todo:
        raise Stop("no entry named %r in the order file" % only)
    for e in todo:
        p = prepare(e)
        st = state.get(e["key"], {})
        note = ""
        if st.get("status") == "done":
            note = "   [state: done, would be skipped]"
        elif st.get("status") == "submitted":
            note = "   [state: submitted, would resume polling without resubmitting]"
        elif st.get("status") == "submitting":
            note = "   [state: interrupted submission, would look it up before resubmitting]"
        out("[%2d/%d] %-10s %s%s" % (e["step"], len(entries), e["kind"], e["name"], note))
        if e["kind"] in ("definition", "problem"):
            path = "/submit-definition" if e["kind"] == "definition" else "/submit-problem"
            out("        POST %s%s   Content-Type: application/json" % (check_url(API_BASE + path), ""))
            out("        body: %s (%d bytes, sha256 %s)" % (e["payload"], len(p["body"]), sha256(p["body"])))
            if e["kind"] == "definition":
                d = p["payload"]
                out("        definition_title: %s" % d["definition_title"])
                out("        definition: %d lines; tags %s; env %s" % (d["definition"].count("\n"), d.get("tags"), d.get("env")))
            else:
                q = p["payload"]["problems"][0]
                out("        theorem_title: %s" % q["theorem_title"])
                out("        source: %s; tags %s; env %s" % (q.get("source"), q.get("tags"), p["payload"].get("env")))
                out("        preamble: %d import lines; formal_statement: %d lines" % (
                    q["preamble"].count("\nimport ") + 1, q["formal_statement"].count("\n") + 1))
            out("        then poll GET %s/publish-jobs/<job_id> until %s" % (API_BASE, " | ".join(sorted(JOB_FINAL))))
            if verbose:
                out(p["body"].decode("utf-8"))
        else:
            tid = state.get("problem:" + e["name"], {}).get("theorem_id") or "<theorem_id of the problem published in the step before>"
            out("        POST %s   Content-Type: multipart/form-data" % check_url(API_BASE + "/verify"))
            out("        fields: theorem_id=%s  proof_type=prove" % tid)
            out("        file: solution.lean <- %s (%d bytes, sha256 %s)" % (e["lean"], len(p["lean"]), sha256(p["lean"])))
            out("        then poll GET %s/verify?submission_id=<submission_id> until %s (success: %s)" % (
                API_BASE, " | ".join(sorted(SUB_FINAL)), SUB_OK))
            if verbose:
                out(p["lean"].decode("utf-8"))
        out("        platform modules imported: %d" % len(e["imports"]))
    out("")
    out("%d entries checked; payload files are consistent with the Lean files" % len(todo))


# ---------------------------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------------------------

def read_key_file():
    path = os.path.expanduser(KEY_FILE)
    if not os.path.exists(path):
        raise Stop("no API key at %s (log in at https://prove2.me, account menu, API key)" % KEY_FILE)
    try:
        mode = os.stat(path).st_mode & 0o077
        if mode:
            sys.stderr.write("warning: %s is readable by other users (chmod 600 it)\n" % KEY_FILE)
    except OSError:
        pass
    with open(path, encoding="utf-8") as f:
        key = f.read().strip()
    if not key:
        raise Stop("%s is empty" % KEY_FILE)
    return key


def main(argv=None):
    ap = argparse.ArgumentParser(description="Upload the TypeDensity bundle to Prove2Me (see the module docstring).")
    ap.add_argument("--order", required=True, help="order file written by build_bundle.py (ORDER.json in the work directory)")
    ap.add_argument("--state", help="state file (default: upload_state.<variant>.json next to the order file)")
    ap.add_argument("--dry-run", action="store_true", help="print what would be sent; no network access, no key")
    ap.add_argument("--verbose", action="store_true", help="with --dry-run: print full request bodies")
    ap.add_argument("--only", metavar="NAME", help="process only the entries with this name")
    ap.add_argument("--poll-interval", type=float, default=5.0, help="seconds between polls at first (default 5)")
    ap.add_argument("--poll-timeout", type=float, default=3600.0, help="seconds to wait for one job (default 3600)")
    ap.add_argument("--platform-version", metavar="V", help="acknowledge that the platform reports version V instead of " + DOCS_VERSION)
    ap.add_argument("--adopt", metavar="KIND:NAME=ID", action="append", default=[],
                    help="record a job_id (definition/problem) or submission_id (solution) found by hand")
    ap.add_argument("--resubmit", metavar="KIND:NAME", action="append", default=[],
                    help="forget an interrupted or failed attempt so that the entry is submitted again")
    args = ap.parse_args(argv)
    try:
        order, entries = load_order(args.order)
        variant = order.get("variant", "default")
        state_path = args.state or os.path.join(os.path.dirname(os.path.abspath(args.order)),
                                                "upload_state.%s.json" % variant)
        if args.dry_run:
            dry_run(order, entries, state_path, args.only, args.verbose)
            return 0
        if order.get("api_base") and order["api_base"] != API_BASE:
            raise Stop("the order file names another API base (%s)" % order["api_base"])
        state = State(state_path, variant)
        keys = {e["key"]: e for e in entries}
        for spec in args.adopt:
            k, _, ident = spec.partition("=")
            if k not in keys or not ident:
                raise Stop("--adopt expects KIND:NAME=ID with an entry of the order file, got %r" % spec)
            field = "submission_id" if keys[k]["kind"] == "solution" else "job_id"
            state.update(k, status="submitted", **{field: ident})
        for k in args.resubmit:
            if k not in keys:
                raise Stop("--resubmit expects KIND:NAME of an entry of the order file, got %r" % k)
            if state.get(k).get("status") == "done":
                raise Stop("%s is done; it cannot be submitted again" % k)
            state.update(k, status="retry", job_id=None, submission_id=None)
        up = Uploader(entries, state, Transport(), read_key_file, poll_interval=args.poll_interval,
                      poll_timeout=args.poll_timeout, accept_version=args.platform_version)
        up.run(args.only)
        return 0
    except Ambiguous as e:
        sys.stderr.write("STOPPED (the last request may or may not have reached the platform): %s\n"
                         "Rerun: the entry is marked as interrupted and is looked up before anything is sent again.\n" % e)
        return 1
    except Stop as e:
        sys.stderr.write("STOPPED: %s\n" % e)
        return 1
    except KeyboardInterrupt:
        sys.stderr.write("interrupted; rerun to resume from the state file\n")
        return 130


if __name__ == "__main__":
    sys.exit(main())
