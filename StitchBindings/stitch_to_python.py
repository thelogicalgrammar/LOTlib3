from pprint import pprint
import ast
import re
import numpy as np
from copy import deepcopy


def parse(expr):
    tokens = expr.replace('(', ' ( ').replace(')', ' ) ').split()
    def read_from_tokens(tokens):
        if len(tokens) == 0:
            raise SyntaxError('unexpected EOF')
        token = tokens.pop(0)
        if token == '(':
            L = []
            while tokens[0] != ')':
                L.append(read_from_tokens(tokens))
            tokens.pop(0)  # pop off ')'
            return L
        elif token == ')':
            raise SyntaxError('unexpected )')
        else:
            return token
    return read_from_tokens(tokens)


def generate_python_code(expression):
    if isinstance(expression, list):
        if len(expression) == 1:
            return generate_python_code(expression[0])
        else:
            args_strings = f'{generate_python_code(expression[0])}'
            for x in expression[1:]:
                args_strings += f'({generate_python_code(x)})'
            return args_strings
    else:
        return str(expression)


def translate(text, conversion_dict, before=None):
    """
    Translate words from a text using a conversion dictionary

    Arguments:
        text: the text to be translated
        conversion_dict: the conversion dictionary
        before: a function to transform the input
        (by default it will to a lowercase)
    """
    # if empty:
    if not text: return text
    # preliminary transformation:
    before = before or str.lower
    t = before(text)
    for key, value in conversion_dict.items():
        t = t.replace(key, value)
    return t


def add_variables(formula, varstitch, varpython, variables=None):
    """
    stitch uses De Bruijn variables, but python
    needs explicit variables after lambdas. 
    This takes a parsed formula (recursive list of lists format)
    and adds the variables explicitly to lambdas.
    """
    if variables is None:
        variables = []
    if isinstance(formula, list):
        operator, *arguments = formula
        if operator=="lam":
            newvar = f"{varpython}{len(variables)+1}"
            operator = f"lambda {newvar}: "
            variables = [newvar] + variables
        return [
            operator, 
            *[
                add_variables(
                    x,
                    variables=variables,
                    varstitch=varstitch, 
                    varpython=varpython, 
                )
                for x in arguments
            ]
        ]
    elif isinstance(formula, str) and formula.startswith(varstitch):
        return variables[int(formula[1:])]
    else:
        return formula


def stitch_to_python(expr, primitive_replacements=None, 
                     varstitch='$', varpython='x'):
    if primitive_replacements is None:
        primitive_replacements = dict()
    expr = translate(
        expr, 
        primitive_replacements
    )
    expr = parse(expr)
    expr = add_variables(
        expr, 
        varstitch=varstitch,
        varpython=varpython
    )
    expr = generate_python_code(expr)
    return expr


def abstraction_to_python(a):
    """
    convert from stitch found abstraction
    to abstraction in python notation
    """
    a = a.split(':=')[1].strip()
    a = a.replace('#', 'y')
    indices_vars = list(map(
        int, 
        re.findall(
            r'(?<=y)[\d]+',
            a
        )
    ))
    prefix = ''
    if len(indices_vars) > 0:
        var_max = max(indices_vars)
        prefix = ''.join([
            f'lambda y{i}: '
            for i in range(var_max+1)
        ])
    return prefix + stitch_to_python(a)