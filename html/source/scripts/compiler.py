# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
import fcntl
import os
import subprocess
from pathlib import Path
import sys
compiler, lock_path, *arguments = sys.argv[1:]
command = [compiler, *arguments]
cache_available = any((Path(entry) / 'Mathlib' / 'Analysis' / 'SpecialFunctions' / 'Log' / 'Basic.olean').is_file()
                      for entry in os.environ.get('LEAN_PATH', '').split(':'))
if not cache_available and not os.environ.get('NONADDITIVITY_LEAN_PATH'):
    elan_lake = Path.home() / '.elan' / 'bin' / 'lake'
    command = [str(elan_lake) if elan_lake.is_file() else 'lake', 'env', 'lean', *arguments]
with open(lock_path, 'a') as lock_file:
    if os.environ.get('NONADDITIVITY_PARALLEL') != '1':
        fcntl.flock(lock_file, fcntl.LOCK_EX)
    try:
        result = subprocess.run(command, check=False)
    except KeyboardInterrupt:
        sys.exit(130)
    sys.exit(result.returncode)
