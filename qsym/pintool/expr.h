#ifndef QSYM_EXPR_H_
#define QSYM_EXPR_H_

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

extern z3::context *g_z3_context;

const INT32 kMaxDepth = 100;

enum Kind {
  Bool, // 0
  Constant, // 1
  Read, // 2
  Concat, // 3
  Extract, // 4

  ZExt, // 5
  SExt, // 6

  // Arithmetic
  Add, // 7
  Sub, // 8
  Mul, // 9
  UDiv, // 10
  SDiv, // 11
  URem, // 12
  SRem, // 13
  Neg,  // 14

  // Bit
  Not, // 15
  And, // 16
  Or, // 17
  Xor, // 18
  Shl, // 19
  LShr, // 20
  AShr, // 21

  // Compare
  Equal, // 22
  Distinct, // 23
  Ult, // 24
  Ule, // 25
  Ugt, // 26
  Uge, // 27
  Slt, // 28
  Sle, // 29
  Sgt, // 30
  Sge, // 31

  // Logical
  LOr, // 32
  LAnd, // 33
  LNot, // 34

  // Special
  Ite, // 35

  // Virtual operation
  Rol,
  Ror,
  Invalid
};

Kind swapKind(Kind kind);
Kind negateKind(Kind kind);
bool isNegatableKind(Kind kind);

}

#include "expr_sub.h"

namespace qsym {

typedef std::weak_ptr<Expr> WeakExprRef;
typedef std::vector<WeakExprRef> WeakExprRefVectorTy;

template <class T>
inline std::shared_ptr<T> castAs(ExprRef e) {
  if (T::classOf(*e))
    return static_pointer_cast<T>(e);
  else
    return NULL;
}

template <class T>
inline std::shared_ptr<T> castAsNonNull(ExprRef e) {
  assert(T::classOf(*e));
  return static_pointer_cast<T>(e);
}

class ExprBuilder;
class IndexSearchTree;

typedef std::set<INT32> DepSet;

}

#include "libsym.h"

namespace qsym {

class Expr : public DependencyNode {
  public:
    Expr(Kind kind, UINT32 bits);
    virtual ~Expr();
    Expr(const Expr& that) = delete;

    void setShadow(void* s) {
      shadow = s;
    }

    void* getShadow() const {
      return shadow;
    }

    XXH32_hash_t hash();

    Kind kind() const {
      if (shadow == nullptr) abort();
      Kind k = (Kind) getKind(shadow);
      return k;
    }

    UINT32 bits() const {
      if (shadow == nullptr) abort();
      uint32_t s = getBits(shadow);
      return s;
    }

    UINT32 bytes() const {
      // utility function to convert from bits to bytes
      assert(bits() % CHAR_BIT == 0);
      return bits() / CHAR_BIT;
    }

    inline ExprRef getChild(UINT32 index) const {
      return getChildExpr(shadow, index);
    }

    inline INT32 num_children() const {
      return getNumChildExpr(shadow);
    }

    inline ExprRef getFirstChild() const {
      return getChild(0);
    }

    inline ExprRef getSecondChild() const {
      return getChild(1);
    }

    inline ExprRef getLeft() const {
      return getFirstChild();
    }

    inline ExprRef getRight() const {
      return getSecondChild();
    }

    INT32 depth();

    bool isConcrete() const {
      return isConcreteExpr(shadow);
    }

    bool isConstant() const {
      return kind() == Constant;
    }

    bool isBool() const {
      return kind() == Bool;
    }

    bool isZero() const;
    bool isAllOnes() const;
    bool isOne() const;

    DepSet& getDeps() {
      if (deps_ == NULL) {
        deps_ = new DepSet();
        DepSet& deps = *deps_;
        for (INT32 i = 0; i < num_children(); i++) {
          DepSet& other = getChild(i)->getDeps();
          deps.insert(other.begin(), other.end());
        }
      }
      return *deps_;
    }

    DependencySet computeDependencies() override;

    UINT32 countLeadingZeros() {
      if (leading_zeros_ == (UINT32)-1)
        leading_zeros_ = _countLeadingZeros();
      return leading_zeros_;
    }
    virtual UINT32 _countLeadingZeros() const { return 0; }
    virtual void print(ostream& os=std::cerr, UINT depth=0) const;
    void printConstraints();
    std::string toString() const;
    void simplify();

    z3::expr& toZ3Expr(bool verbose=false) {
      if (expr_ == NULL) {
        z3::expr z3_expr = toZ3ExprRecursively(verbose);
        expr_ = new z3::expr(z3_expr);
      }
      return *expr_;
    }

    friend bool equalMetadata(const Expr& l, const Expr& r) {
      return (const_cast<Expr&>(l).hash() == const_cast<Expr&>(r).hash()
          && l.kind() == r.kind()
          && l.num_children() == r.num_children()
          && l.bits() == r.bits()
          && l.equalAux(r));
    }

    friend bool equalShallowly(const Expr& l, const Expr& r) {
      // Check equality only in 1 depth if not return false
      if (!equalMetadata(l, r))
        return false;

      // If one of childrens is different, then false
      for (INT32 i = 0; i < l.num_children(); i++) {
        if (l.getChild(i) != r.getChild(i))
          return false;
      }
      return true;
    }

    friend bool operator==(const Expr& l, const Expr& r) {
      // 1. if metadata are different -> different
      if (!equalMetadata(l, r))
        return false;

      // 2. if metadata of children are different -> different
      for (INT32 i = 0; i < l.num_children(); i++) {
        if (!equalMetadata(*l.getChild(i), *r.getChild(i)))
          return false;
      }

      // 3. if all childrens are same --> same
      for (INT32 i = 0; i < l.num_children(); i++) {
        if (l.getChild(i) != r.getChild(i)
            && *l.getChild(i) != *r.getChild(i))
          return false;
      }
      return true;
    }

    friend bool operator!=(const Expr& l, const Expr& r) {
      return !(l == r);
    }

    inline void addChild(ExprRef e) {
      abort();
      // children_.push_back(e);
      // if (!e->isConcrete())
      //  isConcrete_ = false;
    }
    void addUse(WeakExprRef e) { 
      uses_.push_back(e); 
    }

    void addConstraint(Kind kind, llvm::APInt rhs, llvm::APInt adjustment);
    RangeSet* getRangeSet(bool is_unsigned) const { return range_sets[is_unsigned]; }
    void setRangeSet(bool is_unsigned, RangeSet* rs) { range_sets[is_unsigned] = rs; }
    RangeSet* getSignedRangeSet() const { return getRangeSet(false); }
    RangeSet* getUnsignedRangeSet() const { return getRangeSet(true); }

    /*
    // not used by SymCC

    void concretize() {
      if (!isConcrete()) {
        isConcrete_ = true;
        for (auto it = uses_.begin(); it != uses_.end(); it++) {
          WeakExprRef& ref = *it;
          if (ref.expired())
            continue;
          ref.lock()->tryConcretize();
        }
      }
    }

    void tryConcretize() {
      if (isConcrete())
        return;

      for (INT32 i = 0; i < num_children(); i++) {
        ExprRef e = getChild(i);
        if (!e->isConcrete())
          return;
      }

      concretize();
    }
    */

    ExprRef evaluate();

  protected:
    void* shadow;
    // Kind kind_;
    // UINT32 bits_;
    // std::vector< ExprRef > children_;
    z3::context& context_;
    z3::expr *expr_;
    // XXH32_hash_t* hash_;
    RangeSet *range_sets[2];

    // concretization
    // bool isConcrete_;

    // INT32 depth_;
    DepSet* deps_;
    WeakExprRefVectorTy uses_;
    UINT32 leading_zeros_;
    ExprRef evaluation_;

    void printChildren(ostream& os, bool start, UINT depth) const;

    virtual bool printAux(ostream& os) const {
      return false;
    }

    void addConstraint(RangeSet& rs,
        Kind kind,
        llvm::APInt& rhs,
        llvm::APInt& adjustment);
    void addConstraint(bool is_unsigned,
        Kind kind,
        llvm::APInt& rhs,
        llvm::APInt& adjustment);

    virtual std::string getName() const = 0;
    virtual z3::expr toZ3ExprRecursively(bool verbose) = 0;
    // virtual void hashAux(XXH32_state_t* state) { return; }
    virtual bool equalAux(const Expr& other) const { return true; }
    virtual ExprRef evaluateImpl() = 0;

}; // class Expr

struct ExprRefHash {
  XXH32_hash_t operator()(const ExprRef e) const {
    return const_pointer_cast<Expr>(e)->hash();
  }
};

struct ExprRefEqual {
  bool operator()(const ExprRef l,
      const ExprRef r) const {
    return l == r || equalShallowly(*l, *r);
  }
};

class ConstantExpr : public Expr {
public:
  ConstantExpr(ADDRINT value, UINT32 bits) :
    Expr(Constant, bits)
    //, value_(bits, value) 
    {}

  ConstantExpr(const llvm::APInt& value, UINT32 bits) :
    Expr(Constant, bits)
    //, value_(value) 
    {}

  inline llvm::APInt value() const { return llvm::APInt(getConcreteIntegerValue(shadow), bits()); }
  inline bool isZero() const { return value() == 0; }
  inline bool isOne() const { return value() == 1; }
  inline bool isAllOnes() const { return value().isAllOnesValue(); }
  static bool classOf(const Expr& e) { return e.kind() == Constant; }
  UINT32 getActiveBits() const { return value().getActiveBits(); }
  void print(ostream& os, UINT depth) const override;
  UINT32 _countLeadingZeros() const override {
    return value().countLeadingZeros();
  }

protected:
  std::string getName() const override {
    return "Constant";
  }

  bool printAux(ostream& os) const override {
    os << "value=0x" << LLVMIntToString(value(), 16)
      << ", bits=" << bits();
    return true;
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    if (value().getNumWords() == 1)
      return context_.bv_val((__uint64)value().getZExtValue(), bits());
    else
      return context_.bv_val(LLVMIntToString(value(), 10).c_str(), bits());
  }

  /*
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state,
        value().getRawData(),
        value().getNumWords() * sizeof(uint64_t));
  }
  */

  bool equalAux(const Expr& other) const override {
    const ConstantExpr& typed_other = static_cast<const ConstantExpr&>(other);
    return value() == typed_other.value();
  }

  ExprRef evaluateImpl() override;
  // llvm::APInt value_
};


class NonConstantExpr : public Expr {
  public:
    using Expr::Expr;
    static bool classOf(const Expr& e) { return !ConstantExpr::classOf(e); }
};

class UnaryExpr : public NonConstantExpr {
public:
  UnaryExpr(Kind kind, ExprRef e, UINT32 bits)
    : NonConstantExpr(kind, bits) {
      // addChild(e);
    }
  UnaryExpr(Kind kind, ExprRef e)
    : UnaryExpr(kind, e, e->bits()) {}

  ExprRef expr() const { return getFirstChild(); }

protected:
  ExprRef evaluateImpl() override;
};

class BinaryExpr : public NonConstantExpr {
public:
  BinaryExpr(Kind kind, ExprRef l,
      ExprRef r, UINT32 bits) :
    NonConstantExpr(kind, bits) {
      // addChild(l);
      // addChild(r);
      QSYM_ASSERT(l->bits() == r->bits());
    }

  BinaryExpr(Kind kind,
      ExprRef l,
      ExprRef r) :
    BinaryExpr(kind, l, r, l->bits()) {}

  void print(ostream& os, UINT depth, const char* op) const;
protected:
  ExprRef evaluateImpl() override;
};

class LinearBinaryExpr : public BinaryExpr {
using BinaryExpr::BinaryExpr;
};

class NonLinearBinaryExpr : public BinaryExpr {
using BinaryExpr::BinaryExpr;
};

class CompareExpr : public LinearBinaryExpr {
public:
  CompareExpr(Kind kind,
      ExprRef l,
      ExprRef r) :
    LinearBinaryExpr(kind, l, r, 1) {
      assert(l->bits() == r->bits());
    }
};

class BoolExpr : public NonConstantExpr {
public:
  BoolExpr(bool value) :
    NonConstantExpr(Bool, 1)
    // , value_(value) 
    {}

  inline bool value() const { return getBoolValue(shadow); }
  static bool classOf(const Expr& e) { return e.kind() == Bool; }

protected:
  std::string getName() const override {
    return "Bool";
  }

  bool printAux(ostream& os) const override {
    os << "value=" << value();
    return true;
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return context_.bool_val(value());
  }

  /*
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state, &value_, sizeof(value_));
  }
  */

  bool equalAux(const Expr& other) const override {
    const BoolExpr& typed_other = static_cast<const BoolExpr&>(other);
    return value() == typed_other.value();
  }

  ExprRef evaluateImpl() override;
  // bool value_;
};


class ReadExpr : public NonConstantExpr {
public:
  ReadExpr(UINT32 index)
    : NonConstantExpr(Read, 8)// , index_(index) 
  {
    deps_ = new DepSet();
    deps_->insert(index);
    // isConcrete_ = false;
  }

  std::string getName() const override {
    return "Read";
  }

  inline UINT32 index() const { 
    return getReadIndex(shadow);
  }
  static bool classOf(const Expr& e) { return e.kind() == Read; }

protected:
  bool printAux(ostream& os) const override {
    os << "index=" << hexstr(index());
    return true;
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    z3::symbol symbol = context_.int_symbol(index());
    z3::sort sort = context_.bv_sort(8);
    return context_.constant(symbol, sort);
  }

  /*
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state, &index_, sizeof(index_));
  }
  */

  bool equalAux(const Expr& other) const override {
    const ReadExpr& typed_other = static_cast<const ReadExpr&>(other);
    return index() == typed_other.index();
  }

  ExprRef evaluateImpl() override;
  // UINT32 index_;
};

class ConcatExpr : public NonConstantExpr {
public:
  ConcatExpr(ExprRef l, ExprRef r)
    : NonConstantExpr(Concat, l->bits() + r->bits()) {
    // addChild(l);
    // addChild(r);
  }

  void print(ostream& os, UINT depth) const override;

  std::string getName() const override {
    return "Concat";
  }

  static bool classOf(const Expr& e) { return e.kind() == Concat; }
  UINT32 _countLeadingZeros() const override {
    UINT32 result = getChild(0)->countLeadingZeros();
    if (result == getChild(0)->bits())
      result += getChild(1)->countLeadingZeros();
    return result;
  }

protected:
  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::concat(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }

  ExprRef evaluateImpl() override;
};

class ExtractExpr : public UnaryExpr {
public:
  ExtractExpr(ExprRef e, UINT32 index, UINT32 bits)
  : UnaryExpr(Extract, e, bits) //, index_(index) 
  {
    assert(bits + index <= e->bits());
  }

  UINT32 index() const { return getExtractIndex(shadow); }
  ExprRef expr() const { return getFirstChild(); }
  static bool classOf(const Expr& e) { return e.kind() == Extract; }

protected:
  std::string getName() const override {
    return "Extract";
  }

  bool printAux(ostream& os) const override {
    os << "index=" << index() << ", bits=" << bits();
    return true;
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    z3::expr e = getChild(0)->toZ3Expr(verbose);
    return e.extract(index() + bits() - 1, index());
  }

  /*
  void hashAux(XXH32_state_t* state) override {
    XXH32_update(state, &index_, sizeof(index_));
  }
  */

  bool equalAux(const Expr& other) const override {
    const ExtractExpr& typed_other = static_cast<const ExtractExpr&>(other);
    return index() == typed_other.index();
  }

  ExprRef evaluateImpl() override;

  // UINT32 index_;
};

class ExtExpr : public UnaryExpr {
public:
  using UnaryExpr::UnaryExpr;

  ExprRef expr() const { return getFirstChild(); }
  static bool classOf(const Expr& e) {
    return e.kind() == ZExt || e.kind() == SExt;
  }
};

class ZExtExpr : public ExtExpr {
public:
  ZExtExpr(ExprRef e, UINT32 bits)
    : ExtExpr(ZExt, e, bits) {
    }

  std::string getName() const override {
    return "ZExt";
  }

  static bool classOf(const Expr& e) { return e.kind() == ZExt; }
  UINT32 _countLeadingZeros() const override {
    return bits() - getChild(0)->bits();
  }

protected:
  z3::expr toZ3ExprRecursively(bool verbose) override {
    ExprRef e = getChild(0);
    return z3::zext(e->toZ3Expr(verbose), bits() - e->bits());
  }

  bool printAux(ostream& os) const override {
    os << "bits=" << bits();
    return true;
  }

  ExprRef evaluateImpl() override;
};

class SExtExpr : public ExtExpr {
public:
  SExtExpr(ExprRef e, UINT32 bits)
    : ExtExpr(SExt, e, bits) {
    }

  std::string getName() const override {
    return "SExt";
  }

  static bool classOf(const Expr& e) { return e.kind() == SExt; }

protected:
  bool printAux(ostream& os) const override {
    os << "bits=" << bits();
    return true;
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    ExprRef e = getChild(0);
    return z3::sext(e->toZ3Expr(verbose), bits() - e->bits());
  }

  ExprRef evaluateImpl() override;
};

class NotExpr : public UnaryExpr {
public:
  NotExpr(ExprRef e)
    : UnaryExpr(Not, e) {
    }
  static bool classOf(const Expr& e) { return e.kind() == Not; }

protected:
  std::string getName() const override {
    return "Not";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    ExprRef e = getChild(0);
    return ~e->toZ3Expr(verbose);
  }
};

class AndExpr : public NonLinearBinaryExpr {
public:
  AndExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(And, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == And; }

protected:
  std::string getName() const override {
    return "And";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) & getChild(1)->toZ3Expr(verbose);
  }
};

class OrExpr : public NonLinearBinaryExpr {
public:
  OrExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(Or, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Or; }

protected:
  std::string getName() const override {
    return "Or";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) | getChild(1)->toZ3Expr(verbose);
  }
};

class XorExpr : public NonLinearBinaryExpr {
public:
  XorExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(Xor, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Xor; }

protected:
  std::string getName() const override {
    return "Xor";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) ^ getChild(1)->toZ3Expr(verbose);
  }
};

class ShlExpr : public NonLinearBinaryExpr {
public:
  ShlExpr(ExprRef l, ExprRef r)
    : NonLinearBinaryExpr(Shl, l, r) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Shl; }

protected:
  std::string getName() const override {
    return "Shl";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::shl(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class LShrExpr : public NonLinearBinaryExpr {
public:
  LShrExpr(ExprRef l, ExprRef r)
    : NonLinearBinaryExpr(LShr, l, r) {
    }

  static bool classOf(const Expr& e) { return e.kind() == LShr; }

protected:
  std::string getName() const override {
    return "LShr";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::lshr(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class AShrExpr : public NonLinearBinaryExpr {
public:
  AShrExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(AShr, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == AShr; }

protected:
  std::string getName() const override {
    return "AShr";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::ashr(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class AddExpr : public LinearBinaryExpr {
public:
  AddExpr(ExprRef l, ExprRef h)
    : LinearBinaryExpr(Add, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Add; }
  void print(ostream& os, UINT depth) const override;

protected:
  std::string getName() const override {
    return "Add";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) + getChild(1)->toZ3Expr(verbose);
  }
};

class SubExpr : public LinearBinaryExpr {
public:
  SubExpr(ExprRef l, ExprRef h)
    : LinearBinaryExpr(Sub, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Sub; }

protected:
  std::string getName() const override {
    return "Sub";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) - getChild(1)->toZ3Expr(verbose);
  }

  void print(ostream& os=std::cerr, UINT depth=0) const override;
};

class MulExpr : public NonLinearBinaryExpr {
public:
  MulExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(Mul, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Mul; }
  void print(ostream& os, UINT depth) const override;

protected:
  std::string getName() const override {
    return "Mul";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) * getChild(1)->toZ3Expr(verbose);
  }
};

class UDivExpr : public NonLinearBinaryExpr {
public:
  UDivExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(UDiv, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == UDiv; }
  void print(ostream& os, UINT depth) const override;

protected:
  std::string getName() const override {
    return "UDiv";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::udiv(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class SDivExpr : public NonLinearBinaryExpr {
public:
  SDivExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(SDiv, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == SDiv; }
  void print(ostream& os, UINT depth) const override;

protected:
  std::string getName() const override {
    return "SDiv";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) / getChild(1)->toZ3Expr(verbose);
  }
};

class URemExpr : public NonLinearBinaryExpr {
public:
  URemExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(URem, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == URem; }
  void print(ostream& os, UINT depth) const override;

protected:
  std::string getName() const override {
    return "URem";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::urem(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class SRemExpr : public NonLinearBinaryExpr {
public:
  SRemExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(SRem, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == SRem; }
  void print(ostream& os, UINT depth) const override;

protected:
  std::string getName() const override {
    return "SRem";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::srem(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class NegExpr : public UnaryExpr {
public:
  NegExpr(ExprRef e)
    : UnaryExpr(Neg, e) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Neg; }

protected:
  std::string getName() const override {
    return "Neg";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    ExprRef e = getChild(0);
    return -e->toZ3Expr(verbose);
  }
};

class EqualExpr : public CompareExpr {
public:
  EqualExpr(ExprRef l, ExprRef h)
    : CompareExpr(Equal, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Equal; }

protected:
  std::string getName() const override {
    return "Equal";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) == getChild(1)->toZ3Expr(verbose);
  }
};

class DistinctExpr : public CompareExpr {
public:
  DistinctExpr(ExprRef l, ExprRef h)
    : CompareExpr(Distinct, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Distinct; }

protected:
  std::string getName() const override {
    return "Distinct";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) != getChild(1)->toZ3Expr(verbose);
  }
};

class UltExpr : public CompareExpr {
public:
  UltExpr(ExprRef l, ExprRef h)
    : CompareExpr(Ult, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Ult; }

protected:
  std::string getName() const override {
    return "Ult";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::ult(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class UleExpr : public CompareExpr {
public:
  UleExpr(ExprRef l, ExprRef h)
    : CompareExpr(Ule, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Ule; }

protected:
  std::string getName() const override {
    return "Ule";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::ule(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class UgtExpr : public CompareExpr {
public:
  UgtExpr(ExprRef l, ExprRef h)
    : CompareExpr(Ugt, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Ugt; }

protected:
  std::string getName() const override {
    return "Ugt";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::ugt(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class UgeExpr : public CompareExpr {
public:
  UgeExpr(ExprRef l, ExprRef h)
    : CompareExpr(Uge, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Uge; }

protected:
  std::string getName() const override {
    return "Uge";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::uge(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose));
  }
};

class SltExpr : public CompareExpr {
public:
  SltExpr(ExprRef l, ExprRef h)
    : CompareExpr(Slt, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Slt; }

protected:
  std::string getName() const override {
    return "Slt";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose)
      < getChild(1)->toZ3Expr(verbose);
  }
};

class SleExpr : public CompareExpr {
public:
  SleExpr(ExprRef l, ExprRef h)
    : CompareExpr(Sle, l, h) {
      // setShadow(buildBinaryExpression(ExprRef(this), Sle, l->getShadow(), h->getShadow()));
    }

  static bool classOf(const Expr& e) { return e.kind() == Sle; }

protected:
  std::string getName() const override {
    return "Sle";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose)
      <= getChild(1)->toZ3Expr(verbose);
  }
};

class SgtExpr : public CompareExpr {
public:
  SgtExpr(ExprRef l, ExprRef h)
    : CompareExpr(Sgt, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Sgt; }

protected:
  std::string getName() const override {
    return "Sgt";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) > getChild(1)->toZ3Expr(verbose);
  }
};

class SgeExpr : public CompareExpr {
public:
  SgeExpr(ExprRef l, ExprRef h)
    : CompareExpr(Sge, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == Sge; }

protected:
  std::string getName() const override {
    return "Sge";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) >= getChild(1)->toZ3Expr(verbose);
  }
};

class LAndExpr : public NonLinearBinaryExpr {
public:
  LAndExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(LAnd, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == LAnd; }

protected:
  std::string getName() const override {
    return "LAnd";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) && getChild(1)->toZ3Expr(verbose);
  }
};

class LOrExpr : public NonLinearBinaryExpr {
public:
  LOrExpr(ExprRef l, ExprRef h)
    : NonLinearBinaryExpr(LOr, l, h) {
    }

  static bool classOf(const Expr& e) { return e.kind() == LOr; }

protected:
  std::string getName() const override {
    return "LOr";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return getChild(0)->toZ3Expr(verbose) || getChild(1)->toZ3Expr(verbose);
  }
};

class LNotExpr : public UnaryExpr {
public:
  LNotExpr(ExprRef e)
    : UnaryExpr(LNot, e) {
    }

  static bool classOf(const Expr& e) { return e.kind() == LNot; }

protected:
  std::string getName() const override {
    return "LNot";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    ExprRef e = getChild(0);
    return !e->toZ3Expr(verbose);
  }
};

class IteExpr : public NonConstantExpr {
public:
  IteExpr(ExprRef expr_cond, ExprRef expr_true, ExprRef expr_false)
    : NonConstantExpr(Ite, expr_true->bits()) {
    assert(expr_true->bits() == expr_false->bits());
    // addChild(expr_cond);
    // addChild(expr_true);
    // addChild(expr_false);
  }

  static bool classOf(const Expr& e) { return e.kind() == Ite; }
  ExprRef expr_cond() const { return getChild(0); }
  ExprRef expr_true() const { return getChild(1); }
  ExprRef expr_false() const { return getChild(2); }

protected:
  std::string getName() const override {
    return "Ite";
  }

  z3::expr toZ3ExprRecursively(bool verbose) override {
    return z3::ite(getChild(0)->toZ3Expr(verbose),
        getChild(1)->toZ3Expr(verbose),
        getChild(2)->toZ3Expr(verbose));
  }

  ExprRef evaluateImpl() override;
};

// utility functions
bool isZeroBit(ExprRef e, UINT32 idx);
bool isOneBit(ExprRef e, UINT32 idx);
bool isRelational(const Expr* e);
bool isConstant(ExprRef e);
bool isConstSym(ExprRef e);
UINT32 getMSB(ExprRef e);

} // namespace qsym
#endif // QSYM_EXPR_H_
