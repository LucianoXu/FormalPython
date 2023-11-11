from __future__ import annotations

from typing import Type, Tuple

# the basic REM error
class REM_Error(Exception):
    pass

# the error during parser construction
class REM_Parser_Building_Error(REM_Error):
    pass

# the error of wrong syntax when parsing
class REM_Syntax_Error(REM_Error):
    pass

def REM_type_check(obj : object, target_type : Type | Tuple[Type, ...], error_type : Type[REM_Error] = REM_Error) -> None:

    if isinstance(target_type, tuple):
        for t in target_type:
            if isinstance(obj, t):
                return
        
        raise error_type("REM-type-check: The parameter expression '" + str(obj) + "' should be within type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

    elif not isinstance(obj, target_type):
        raise error_type("REM-type-check: The parameter expression '" + str(obj) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

def REM_other_check(expr : bool, reason : str, error_type : Type[REM_Error] = REM_Error) -> None:
    if not expr:
        raise error_type("REM-other-check: Rem does not accept because: \n\n{}".format(reason))

def REM_warning(msg : str):
    print(f"Rem WARNING: {msg}")