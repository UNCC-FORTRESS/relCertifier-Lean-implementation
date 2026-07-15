#!/usr/bin/env python3
"""Import-direction audit for the trust boundary.

Files under RelCertifier/Trusted/ may import: other Trusted modules, Core, Checker,
and non-RelCertifier packages. They must NEVER import Proofs, Instances, or Archive —
the trusted surface cannot depend on the things it is supposed to justify.
Exit 1 on any violation.
"""
import os, re, sys

ALLOWED = ("RelCertifier.Trusted.", "RelCertifier.Core.", "RelCertifier.Checker.")
bad = []
root = os.path.join(os.path.dirname(__file__), "..", "RelCertifier", "Trusted")
for dirpath, _, files in os.walk(root):
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(dirpath, f)
        for imp in re.findall(r"^import (RelCertifier\.\S+)", open(p).read(), re.M):
            if not imp.startswith(ALLOWED):
                bad.append(f"{p}: imports {imp}")
if bad:
    print("TRUST-BOUNDARY VIOLATIONS:")
    for b in bad:
        print(" ", b)
    sys.exit(1)
print("trust boundary clean: Trusted/ imports only Trusted/Core/Checker")
