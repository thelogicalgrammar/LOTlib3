import ast
import re
import numpy as np
from copy import deepcopy


def remove_variables(formula, varstitch, varpython, variables=None):
    if variables is None:
        variables = []

    if isinstance(formula, list):
        # structure is [[fname arg1], arg2]]
        if isinstance(formula[0], list):
            return remove_variables(
                [*formula[0], *formula[1:]],
                variables=variables,
                varstitch=varstitch, 
                varpython=varpython, 
            )
        else:
            operator, *arguments = formula
            if operator.replace(' ', '').startswith('lambda:'):
                # if there is a lambda with
                # 0 arguments, do not add
                # a variable
                assert len(arguments)==1
                return remove_variables(
                    arguments[0],
                    variables=variables,
                    varstitch=varstitch, 
                    varpython=varpython, 
                )
            elif operator.startswith("lambda"):
                newvar = operator.strip()[:-1].split()[1]
                operator = f"lam "
                variables = [newvar] + variables
            return [
                operator, 
                *[
                    remove_variables(
                        x,
                        variables=variables,
                        varstitch=varstitch, 
                        varpython=varpython, 
                    )
                    for x in arguments
                ]
            ]
    # variable!
    elif isinstance(formula, str) and formula.startswith(varpython):
        # return variables[int(formula[1:])]
        return f'{varstitch}{variables.index(formula)}'
    # function name or argument name!
    else:
        return formula


def visit_node(node):
    """
    Visit AST node and return appropriate value.
    """
    if isinstance(node, ast.Call):
        func_name = visit_node(node.func)
        args = [visit_node(arg) for arg in node.args]
        return [func_name] + args
    elif isinstance(node, ast.Name):
        return node.id
    elif isinstance(node, ast.Lambda):
        return [f'lambda {", ".join([arg.arg for arg in node.args.args])}:', visit_node(node.body)]
    elif isinstance(node, ast.Constant):
        return str(node.value)
    else:
        raise ValueError(f"Unhandled node type: {type(node)}")


def parse_function_calls(expression):
    """
    Parse function call expressions into nested list of function names and arguments.
    """
    parsed_expression = ast.parse(expression, mode='eval')
    return visit_node(parsed_expression.body)
    

def parsed_to_stitch(parsed):
    if isinstance(parsed, list):
        op, *args = parsed
        return f'({op.strip()} {" ".join([parsed_to_stitch(x) for x in args])})'
    else:
        return str(parsed)


def python_to_stitch(expr, varstitch='$', varpython='x'):
    return parsed_to_stitch(
        remove_variables(
            parse_function_calls(
                expr
            ),
            varstitch=varstitch,
            varpython=varpython
        )
    )   