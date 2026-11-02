"""Direct rider append via the Register API (L2 fallback while the MCP bridge
is stalled). Idempotent: append_rider is UNIQUE(entry_id, rider_id), so a
re-run after a half-landed call is a no-op. Usage: append_rider.py <file> [rider_id]
"""
import sys
from pathlib import Path

from multiaim_agents.memory.palimpsest import get_soma
from multiaim_agents.register import Register

path = Path(sys.argv[1])
text = path.read_text().strip()
rider_id = sys.argv[2] if len(sys.argv) > 2 else path.stem[:120]

reg = Register(db=get_soma())
ok = reg.append_rider(2125607854, text, rider_id=rider_id)
print(f"appended={ok} rider_id={rider_id}")
