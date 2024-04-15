

from .term import *
from .context import *
from .environment import *
from .typing_rule import *
from .conversion_rule import *

from .theory import RemCoC

coc = RemCoC()

coc.gen_doc(__file__ + "rule.txt")