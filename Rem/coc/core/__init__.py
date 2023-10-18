
# the coc system
from .rem_sys_head import rem_coc

from .term import *
from .context import *
from .environment import *
from .typing_rule import *
from .conversion_rule import *

# check the system
Rem_system_build(
    rem_coc, 
    file = __file__
)