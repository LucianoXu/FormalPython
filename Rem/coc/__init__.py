from .core import *

from . import parsing

# check the system
Rem_system_build(
    rem_coc, 
    file=__file__,
    build_parser=True
)