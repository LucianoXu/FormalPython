import numpy as np

from Rem import *
from Rem import uLC

if __name__ == "__main__":
    lc = RemVTerm.verify(uLC.F_uLC())
    print(uLC.parser("λy.λx.(x y)"))