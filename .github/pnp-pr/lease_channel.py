"""Transfer a desk lease to one protected Actions job using an ephemeral recipient key."""
import argparse
import base64
import json
import os
from pathlib import Path
import re
import subprocess
import time

from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

REPO = "ChoiCube84/pequalnp-proofs"
BRANCH = "codex-pr-cli"
MAILBOX = ".github/codex-lease/envelope.json"
STATUS = "codex-pr-cli/lease-key"


def encode(data):
    return base64.b64encode(data).decode("ascii")


def public_bytes(key):
    return key.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)


def shared_key(private, public, context):
    peer = X25519PublicKey.from_public_bytes(base64.b64decode(public, validate=True))
    return HKDF(algorithm=hashes.SHA256(), length=32, salt=None, info=context).derive(private.exchange(peer))


def associated(sha, run, attempt):
    if not re.fullmatch(r"[0-9a-f]{40}", sha) or not all(re.fullmatch(r"[0-9]+", s) for s in [run, attempt]):
        raise ValueError("Unexpected Actions run identity.")
    return f"{REPO}/{BRANCH}/{sha}/{run}/{attempt}".encode("ascii")


def seal(message, recipient, context):
    private = X25519PrivateKey.generate()
    nonce = os.urandom(12)
    body = AESGCM(shared_key(private, recipient, context)).encrypt(nonce, message, context)
    return {"run": context.decode("ascii"), "sender": encode(public_bytes(private)), "packet": encode(nonce + body)}


def unseal(envelope, private, context):
    if envelope.get("run") != context.decode("ascii"):
        return None
    packet = base64.b64decode(envelope["packet"], validate=True)
    return AESGCM(shared_key(private, envelope["sender"], context)).decrypt(packet[:12], packet[12:], context)


def receive(destination):
    sha, run, attempt = (os.environ[k] for k in ["GITHUB_SHA", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"])
    context = associated(sha, run, attempt)
    private = X25519PrivateKey.generate()
    status = {"state": "success", "context": STATUS, "description": f"{run} {attempt} {encode(public_bytes(private))}"}
    subprocess.run(["gh", "api", "--method", "POST", f"repos/{REPO}/statuses/{sha}", "--input", "-"],
                   input=json.dumps(status).encode(), stdout=subprocess.DEVNULL, check=True)
    for _ in range(44):
        cmd = ["gh", "api", f"repos/{REPO}/contents/{MAILBOX}?ref={BRANCH}", "--jq", ".content"]
        resp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        if resp.returncode == 0:
            payload = json.loads(base64.b64decode(resp.stdout))
            message = unseal(payload, private, context)
            if message is not None:
                if not re.fullmatch(rb"[A-Za-z0-9_-]{8,180}", message):
                    raise ValueError("The desk lease has an unexpected format.")
                destination.write_bytes(message)
                return
        time.sleep(4)
    raise SystemExit("No lease arrived for this Actions run.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    receive(args.output)


if __name__ == "__main__":
    main()
