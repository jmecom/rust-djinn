#!/usr/bin/env python3
"""Drive rust-djinn-lsp over stdio like an editor would, and print what it sends.

usage: lsp-check.py <path to rust-djinn-lsp> <spec.rs> [command ...]
"""
import json, os, pathlib, subprocess, sys, threading, time

server, spec = sys.argv[1], os.path.abspath(sys.argv[2])
commands = sys.argv[3:]
proc = subprocess.Popen([server], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
lock = threading.Lock()
msgs = []
responses = {}

def send(obj):
    data = json.dumps(obj).encode()
    with lock:
        proc.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        proc.stdin.flush()

def reader():
    while True:
        line = proc.stdout.readline()
        if not line:
            return
        if not line.startswith(b"Content-Length:"):
            continue
        n = int(line.split(b":")[1])
        proc.stdout.readline()
        body = json.loads(proc.stdout.read(n))
        msgs.append(body)
        if "id" in body and "method" in body:          # a server→client request
            m = body["method"]
            print(f"<- request {m} {json.dumps(body.get('params'))[:160]}")
            send({"jsonrpc": "2.0", "id": body["id"], "result": {"success": True} if m == "window/showDocument" else None})
        elif "id" in body:
            responses[body["id"]] = body
        else:
            p = body.get("params", {})
            if body["method"] == "textDocument/publishDiagnostics":
                print(f"<- diagnostics ({len(p['diagnostics'])}):")
                for d in p["diagnostics"]:
                    print(f"     L{d['range']['start']['line']+1} sev{d['severity']}: {d['message'].splitlines()[0][:110]}")
            elif body["method"] == "$/progress":
                v = p["value"]
                print(f"<- progress {v['kind']}: {v.get('message', v.get('title', ''))[:110]}")
            elif body["method"] == "window/showMessage":
                print(f"<- showMessage: {p['message'][:300]}")
            elif body["method"] == "window/logMessage":
                pass
            else:
                print(f"<- {body['method']}")

threading.Thread(target=reader, daemon=True).start()
rid = 0
def request(method, params, wait=True):
    global rid
    rid += 1
    send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
    if not wait:
        return None
    for _ in range(600):
        if rid in responses:
            return responses[rid]
        time.sleep(0.05)
    return None

uri = pathlib.Path(spec).as_uri()
init = request("initialize", {"processId": None, "rootUri": None, "capabilities": {"window": {"showDocument": {"support": True}, "workDoneProgress": True}}})
caps = (init or {}).get("result", {}).get("capabilities", {})
for key in ("textDocumentSync", "codeLensProvider", "inlayHintProvider", "executeCommandProvider"):
    if key not in caps:
        print(f"!! initialize result lacks capabilities.{key} (editors would ignore the server)")
print("capabilities:", ", ".join(sorted(caps)))
send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {"uri": uri, "languageId": "rust", "version": 1, "text": open(spec).read()}}})
time.sleep(3)
r = request("textDocument/codeLens", {"textDocument": {"uri": uri}})
print("codeLens:")
for l in (r or {}).get("result", []):
    c = l["command"]
    print(f"     L{l['range']['start']['line']+1} [{c['title']}] -> {c['command']}")
r = request("textDocument/inlayHint", {"textDocument": {"uri": uri}, "range": {"start": {"line": 0, "character": 0}, "end": {"line": 9999, "character": 0}}})
print("inlayHints:")
for h in (r or {}).get("result", []):
    print(f"     L{h['position']['line']+1}:{h['position']['character']} {h['label']}")
for c in commands:
    name, *args = c.split(":")
    print(f"-> executeCommand {name} {args}")
    request("workspace/executeCommand", {"command": name, "arguments": [uri] + args})
    time.sleep(2 if name.startswith("djinn.open") else 60)
request("shutdown", None)
send({"jsonrpc": "2.0", "method": "exit"})
time.sleep(0.5)
proc.terminate()
