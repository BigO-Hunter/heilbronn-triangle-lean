#!/usr/bin/env python3
"""gate_watch.py — daily Heilbronn-triangle gate poll (R2125607854).

Body-native rewrite of gate_watch.sh (Python is the body's language — AGENTS.md;
the lane kit is already Python-first: port_stageb.py, scaffold_stagea.py).
Read-only toward all remotes. Prints ONE status line (or --json).

Exit-code contract (preserved from the .sh; capsules/riders reference it):
    0 = gate CLOSED
    2 = GATE OPEN — file Stage A within hours (stagea/ is green: Race.bound : Bound 0)
    1 = poll error (network / rate-limit / parse)

OPEN signals (either trips exit 2, printed in the status line):
  * profile   — a heilbronn*.json appears in the verifier's profiles/
                (the authoritative signal; the .sh's only trigger)
  * dropdown  — 'heilbronn' appears in the issue-form problem list
                (.github/ISSUE_TEMPLATE/lean-submission.yml). Extension over
                the .sh: this is HOW the subset-sum gate opened (2026-11-01
                21:55Z, form dropdown before any filing). In a first-mover
                race a false-positive costs one human look; a false-negative
                costs the slot.

Dogfooding (body systems exercised on every run):
  * httpx direct against api.github.com — no gh subprocess; works
    unauthenticated (60 req/h), GITHUB_TOKEN/GH_TOKEN env raises the ceiling.
  * soma state key `heilbronn_gate_watch` via get_soma().set_state — written
    ONLY on status change or first run (no state spam on steady polls).
  * --rider: on a CLOSED->OPEN transition, appends a rider to R2125607854 via
    the direct in-process Register API (the R2125607889-proven path — no MCP
    bridge dependency, which can stall during backup cycles).
  * Body-side effects are best-effort but LOUD: a failed rider/state write
    warns on stderr and never masks the gate verdict (Onion: poll is the core,
    body writes are the outer layer).

Usage:
    python3 gate_watch.py            # status line + exit code
    python3 gate_watch.py --json     # machine-readable verdict
    python3 gate_watch.py --rider    # + register rider on OPEN transition

State file: logs/gate_watch_state.json (workspace-local; untracked).
Run: daily by any waking mind (capsule/R2125607854 riders carry the filing
checklist for exit 2).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import httpx

REPO = "bigospeedrun/verifier"
API = "https://api.github.com"
RAW = "https://raw.githubusercontent.com"
WORKSPACE = Path(__file__).resolve().parent
STATE_PATH = WORKSPACE / "logs" / "gate_watch_state.json"
REGISTER_ID = 2125607854
TIMEOUT_S = 25.0


def _client() -> httpx.Client:
    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "multiaim-heilbronn-gate-watch (R2125607854)",
    }
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    return httpx.Client(headers=headers, timeout=TIMEOUT_S, follow_redirects=True)


def _get_json(client: httpx.Client, url: str) -> object:
    resp = client.get(url)
    if resp.status_code in (403, 429) and resp.headers.get("x-ratelimit-remaining") == "0":
        raise RuntimeError(f"GitHub rate limit exhausted (reset {resp.headers.get('x-ratelimit-reset')})")
    resp.raise_for_status()
    return resp.json()


def poll() -> dict:
    """Three read-only probes + the dropdown sensor. Raises RuntimeError on any failure."""
    with _client() as client:
        # 1. profiles/ listing — the authoritative gate signal.
        listing = _get_json(client, f"{API}/repos/{REPO}/contents/profiles")
        if not isinstance(listing, list):
            raise RuntimeError("profiles listing: unexpected response shape")
        names = [str(e.get("name", "")) for e in listing if isinstance(e, dict)]
        heil_profiles = sorted(n for n in names if "heilbronn" in n.lower())

        # 2. issue-form dropdown — the subset-sum gate opened HERE first.
        dropdown_hit = False
        try:
            form = client.get(
                f"{RAW}/{REPO}/main/.github/ISSUE_TEMPLATE/lean-submission.yml"
            )
            form.raise_for_status()
            dropdown_hit = "heilbronn" in form.text.lower()
        except (httpx.HTTPError, RuntimeError):
            # Sensor degradation must not fail the whole poll (Onion): the
            # profile check remains authoritative; mark the sensor unknown.
            dropdown_hit = False

        # 3. recent commits mentioning heilbronn (7-day window) — informational.
        since = (datetime.now(timezone.utc) - timedelta(days=7)).strftime("%Y-%m-%dT%H:%M:%SZ")
        commits = _get_json(client, f"{API}/repos/{REPO}/commits?since={since}&per_page=100")
        heil_commits = sum(
            1
            for c in commits
            if isinstance(c, dict)
            and re.search(r"heilbronn", str(c.get("commit", {}).get("message", "")), re.I)
        ) if isinstance(commits, list) else -1

        # 4. issues mentioning heilbronn — competitor-filing smoke.
        search = _get_json(
            client, f"{API}/search/issues?q=repo:{REPO}+heilbronn+in:title,body&per_page=5"
        )
        heil_issues = int(search.get("total_count", -1)) if isinstance(search, dict) else -1

    open_signals = []
    if heil_profiles:
        open_signals.append("profile:" + ",".join(heil_profiles))
    if dropdown_hit:
        open_signals.append("dropdown")
    return {
        "ts": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%MZ"),
        "gate": "OPEN" if open_signals else "CLOSED",
        "open_signals": open_signals,
        "profiles_total": len(names),
        "heil_profiles": heil_profiles,
        "dropdown_hit": dropdown_hit,
        "commits_7d_heilbronn": heil_commits,
        "issues_heilbronn": heil_issues,
    }


def load_state() -> dict:
    try:
        return json.loads(STATE_PATH.read_text())
    except (OSError, json.JSONDecodeError):
        return {}


def save_state(state: dict) -> None:
    STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
    STATE_PATH.write_text(json.dumps(state, indent=1) + "\n")


def body_side_effects(verdict: dict, prior: dict, *, want_rider: bool = False) -> list[str]:
    """Soma state key + transition rider. Best-effort, loud on failure."""
    notes: list[str] = []
    changed = prior.get("last_status") != verdict["gate"]
    first_run = not prior
    if not (changed or first_run):
        return notes

    # (a) soma state key — visible to any mind via get_state('heilbronn_gate_watch').
    try:
        from multiaim_agents.memory.palimpsest import get_soma

        get_soma().set_state(
            "heilbronn_gate_watch",
            {
                "gate": verdict["gate"],
                "open_signals": verdict["open_signals"],
                "ts": verdict["ts"],
                "action": "FILE STAGE A NOW — see R2125607854 riders for the checklist"
                if verdict["gate"] == "OPEN"
                else "daily poll continues",
            },
        )
        notes.append("soma-state:updated")
    except Exception as exc:  # noqa: BLE001 — loud, never fatal (Onion)
        print(f"WARNING: soma state write failed: {exc}", file=sys.stderr)
        notes.append("soma-state:FAILED")

    # (b) rider on the CLOSED->OPEN transition only (never on steady states).
    if changed and verdict["gate"] == "OPEN" and want_rider:
        try:
            from multiaim_agents.memory.palimpsest import get_soma
            from multiaim_agents.register import Register

            text = (
                f"GATE OPEN detected by gate_watch.py at {verdict['ts']} — "
                f"signals: {'+'.join(verdict['open_signals'])}. FILE STAGE A "
                "within hours: pre-filing checklist in this register's riders "
                "(file.py battle-test on a scratch repo, RUNBOOK entry-name "
                "immunization grep '^theorem Race.bound', strip "
                "VerifierChallenge/VerifierAudit/scratch replicas, pick the "
                "Bound-0 rational form per the live generator). Stage B "
                "(1/10^237) follows per issue #105's answers."
            )
            ok = Register(db=get_soma()).append_rider(
                REGISTER_ID, text, rider_id=f"gate-open-{verdict['ts'].replace(':', '')}"
            )
            notes.append(f"rider:appended={ok}")
        except Exception as exc:  # noqa: BLE001
            print(f"WARNING: rider append failed: {exc}", file=sys.stderr)
            notes.append("rider:FAILED")
    return notes


def main() -> int:
    parser = argparse.ArgumentParser(description="Heilbronn gate poll (see module docstring)")
    parser.add_argument("--json", action="store_true", help="machine-readable verdict")
    parser.add_argument("--rider", action="store_true", help="rider R2125607854 on OPEN transition")
    args = parser.parse_args()

    try:
        verdict = poll()
    except (httpx.HTTPError, RuntimeError, ValueError) as exc:
        ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
        print(f"[{ts}] gate=POLL-ERROR {exc}")
        return 1

    prior = load_state()
    notes = body_side_effects(verdict, prior, want_rider=args.rider)
    save_state(
        {
            "last_status": verdict["gate"],
            "last_run": verdict["ts"],
            "last_open_signals": verdict["open_signals"],
            "runs": int(prior.get("runs", 0)) + 1,
        }
    )

    if verdict["gate"] == "OPEN":
        line = (
            f"[{verdict['ts']}] gate=OPEN SIGNALS={'+'.join(verdict['open_signals'])} "
            f"commits7d={verdict['commits_7d_heilbronn']} issues={verdict['issues_heilbronn']} "
            "— FILE STAGE A NOW (stagea/ green: Race.bound : Bound 0; checklist in R2125607854 riders)"
        )
        code = 2
    else:
        line = (
            f"[{verdict['ts']}] gate=CLOSED profiles={verdict['profiles_total']}/heilbronn=0 "
            f"dropdown={int(verdict['dropdown_hit'])} "
            f"commits7d(heilbronn)={verdict['commits_7d_heilbronn']} "
            f"issues(heilbronn)={verdict['issues_heilbronn']}"
        )
        code = 0
    if notes:
        line += f" [{','.join(notes)}]"
    if args.json:
        print(json.dumps({**verdict, "notes": notes, "exit": code}))
    else:
        print(line)
    return code


if __name__ == "__main__":
    sys.exit(main())
