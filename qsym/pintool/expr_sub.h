#ifndef QSYM_EXPR_SUB_H_
#define QSYM_EXPR_SUB_H_

#include <iostream>
#include <iomanip>
#include <map>
#include <unordered_set>
#include <set>
#include <sstream>
#include <vector>

#include <z3++.h>

#include "common.h"
#include "dependency.h"
#include "third_party/llvm/range.h"

// XXX: need to change into non-global variable?
namespace qsym {

// forward declaration
#define DECLARE_EXPR(cls) \
  class cls; \
  typedef std::shared_ptr<cls> glue(cls, Ref);

DECLARE_EXPR(Expr);
DECLARE_EXPR(ConstantExpr);
DECLARE_EXPR(NonConstantExpr);
DECLARE_EXPR(BoolExpr);

}

#endif