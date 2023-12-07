'''
The builtin term rewriting system in Rem.
'''

from __future__ import annotations

from typing import Union

from types import FunctionType

from .rem import *

from .rem_module import *

'''
The type for a side condition.
- Parameters: matcher, module environment (can be empty)
- return : 
    - RemSubst : accept with new matcher.
    - None : reject.
'''


LHSMatching = Callable[[RemTerm], Union[RemSubst, None]]

SideCond = Callable[[RemSubst], Union[RemSubst, None]]


# a function to calculate the right hand side using the matcher
RHSFun = Callable[[RemSubst], RemTerm]


class RemRedRule:
    def __init__(self, lhs : RemTerm | LHSMatching, 
            rhs : RemTerm | RHSFun, rhs_doc : str = "<rhs>",
            side_cond : SideCond | None = None, side_cond_doc : str = "<side cond>"):
        REM_type_check(lhs, (RemTerm, FunctionType))
        REM_type_check(rhs, (RemTerm, FunctionType))

        self.lhs = lhs
        self.rhs : RHSFun
        if isinstance(rhs, RemTerm):
            self.rhs = lambda subst : subst(rhs)
        else:
            self.rhs = rhs
        self.side_cond = side_cond

        # the doc for RHS
        if isinstance(self.rhs, RemTerm):
            self.rhs_doc = str(self.rhs)
        else:
            self.rhs_doc = rhs_doc

        # the doc for side condition
        if self.side_cond is None:
            self.side_cond_doc = ""
        else:
            self.side_cond_doc = side_cond_doc

    def __str__(self) -> str:
        return f"{self.side_cond_doc} ⊢ {self.lhs} → {self.rhs_doc}"

    def rewrite(self, term : RemTerm, 
                eq_check : Callable[[RemTerm, RemTerm], bool] = lambda a, b: a == b,
                 eq_set : Callable[[RemTerm], List[RemTerm]] | None = None
                 ) -> RemTerm | None:
        '''
        Match and rewrite the term.
        Return the result of rewriting. Return None if not matched.
        '''
        if isinstance(self.lhs, RemTerm):
            matcher = RemMatching.single_match(self.lhs, term, eq_check, eq_set)
        else:
            matcher = self.lhs(term)

        if matcher is None:
            return None
        
        if self.side_cond is None:
            return self.rhs(matcher)
        
        # Check side conditions.
        else:
            new_matcher = self.side_cond(matcher)
            if new_matcher is None:
                return None
            else:
                return self.rhs(new_matcher)

class RemTRS:
    '''
    A term rewriting system

    Note: no renaming is considered here, so the variables in rewriting rules should be always unique, for example "?x".
    '''
    def __init__(self, rules : List[RemRedRule], 
                 eq_check : Callable[[RemTerm, RemTerm], bool] = lambda a, b: a == b,
                 eq_set : Callable[[RemTerm], List[RemTerm]] | None = None):
        '''
        Create a term rewriting system
        '''
        REM_type_check(rules, list)
        for rule in rules:
            REM_type_check(rule, RemRedRule)

        self.rules = rules.copy()

        self.eq_check = eq_check
        self.eq_set = eq_set


    def reduce(self, term : RemTerm) -> RemTerm | None:

        # invocate the verification-free algorithm
        return self.__rewrite_iter(term)
    
    def reduces(self, term : RemTerm, silent : bool = True) -> RemTerm:
   
        # invocate the verification-free algorithm
        
        new_term = term
        step = 0
        while new_term is not None:
            if not silent:
                print(f"[{step}]\t {new_term}\n")
            term = new_term
            new_term = self.__rewrite_iter(term)
            step += 1
        
        return term
    

    def __rewrite_iter(self, term : RemTerm) -> RemTerm | None:
        '''
        Try to rewrite the term once.
        '''

        if isinstance(term, RemVar):
            for rule in self.rules:
                new_term = rule.rewrite(term, self.eq_check, self.eq_set)
                if new_term is not None:
                    return new_term
                
            return None
        
        elif isinstance(term, RemCons):
            # check the parameters
            for i in range(term.fun.arity):
                new_term = self.reduce(term[i])
                if new_term is not None:
                    return term.replace(i, new_term)
                
            # check the function itself
            for rule in self.rules:
                new_term = rule.rewrite(term, self.eq_check, self.eq_set)
                if new_term is not None:
                    return new_term
            
            return None

        else:
            raise Exception()
        
