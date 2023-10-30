from __future__ import annotations

from typing import Type, Tuple

class REM_Error(Exception):
    pass

class REM_SyntaxError(REM_Error):
    pass

def REM_type_check(obj : object, target_type : Type | Tuple[Type, ...]) -> None:

    if isinstance(target_type, tuple):
        for t in target_type:
            if isinstance(obj, t):
                return
        
        raise REM_Error("REM-type-check: The parameter expression '" + str(obj) + "' should be within type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

    elif not isinstance(obj, target_type):
        raise REM_Error("REM-type-check: The parameter expression '" + str(obj) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

def REM_other_check(expr : bool, reason : str) -> None:
    if not expr:
        raise REM_Error("REM-other-check: Rem does not accept because: \n\n{}".format(reason))
