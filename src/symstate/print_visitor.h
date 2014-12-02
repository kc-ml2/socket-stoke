
#ifndef _STOKE_SRC_SYMSTATE_PRINT_VISITOR
#define _STOKE_SRC_SYMSTATE_PRINT_VISITOR

#include "src/symstate/visitor.h"

namespace stoke {

class SymPrintVisitor : public SymVisitor<void> {

public:
  SymPrintVisitor(std::ostream& os) : os_(os) {}

  void visit_binop(const SymBitVectorBinop * const bv) {

    switch(bv->type()) {
    case SymBitVector::AND:
      os_ << "(and ";
      break;
    case SymBitVector::CONCAT:
      os_ << "(concat ";
      break;
    case SymBitVector::DIV:
      os_ << "(div ";
      break;
    case SymBitVector::MINUS:
      os_ << "(minus ";
      break;
    case SymBitVector::MOD:
      os_ << "(mod ";
      break;
    case SymBitVector::MULT:
      os_ << "(mult ";
      break;
    case SymBitVector::OR:
      os_ << "(or ";
      break;
    case SymBitVector::PLUS:
      os_ << "(plus ";
      break;
    case SymBitVector::ROTATE_LEFT:
      os_ << "(rol ";
      break;
    case SymBitVector::ROTATE_RIGHT:
      os_ << "(ror ";
      break;
    case SymBitVector::SHIFT_LEFT:
      os_ << "(<< ";
      break;
    case SymBitVector::SHIFT_RIGHT:
      os_ << "(>> ";
      break;
    case SymBitVector::SIGN_DIV:
      os_ << "(s_div ";
      break;
    case SymBitVector::SIGN_MOD:
      os_ << "(s_mod ";
      break;
    case SymBitVector::SIGN_SHIFT_RIGHT:
      os_ << "(s_shr ";
      break;
    case SymBitVector::XOR:
      os_ << "(xor ";
      break;
    default:
      os_ << "(UNHANDLED_BINOP" << bv->type() << " ";
      assert(false);
    }

    (*this)(bv->a_);
    os_ << " ";
    (*this)(bv->b_);
    os_ << ")";
  }

  /* Visit a binop on a bool */
  void visit_binop(const SymBoolBinop * const b) {

    switch(b->type()) {
    case SymBool::AND:
      os_ << "(and ";
      break;
    case SymBool::IFF:
      os_ << "(== ";
      break;
    case SymBool::IMPLIES:
      os_ << "(implies ";
      break;
    case SymBool::OR:
      os_ << "(or ";
      break;
    case SymBool::XOR:
      os_ << "(xor ";
      break;
    default:
      os_ << "(UNHANDLED_BINOP" << b->type() << " ";
      assert(false);
    }

    (*this)(b->a_);
    os_ << " ";
    (*this)(b->b_);
    os_ << ")";
  }


  void visit_unop(const SymBitVectorUnop * const bv) {

    switch(bv->type()) {
    case SymBitVector::NOT:
      os_ << "!";
      break;
    case SymBitVector::U_MINUS:
      os_ << "-";
      break;
    default:
      os_ << "UNHANDLED_UNOP" << bv->type() << " ";
      assert(false);
    }

    (*this)(bv->bv_);
  }


  void visit_compare(const SymBoolCompare * const b) {

    switch(b->type()) {
    case SymBool::EQ:
      os_ << "(== ";
      break;
    case SymBool::GE:
      os_ << "(>= ";
      break;
    case SymBool::GT:
      os_ << "(> ";
      break;
    case SymBool::LE:
      os_ << "(<= ";
      break;
    case SymBool::LT:
      os_ << "(< ";
      break;
    default:
      os_ << "(UNHANDLED_COMPARE" << b->type() << " ";
      assert(false);
    }

    (*this)(b->a_);
    os_ << " ";
    (*this)(b->b_);
    os_ << ")";

  }

  /** Visit a bit-vector constant */
  void visit(const SymBitVectorConstant * const bv) {
    os_ << "[ ";
    for(size_t i = bv->size_; i > 64; --i)
      os_ << "0, ";
    for(uint64_t mask = (0x8000000000000000 >> (64 - bv->size_)); mask; mask >>= 1) {
      os_ << (bv->constant_ & mask ? 1 : 0);
      if(mask > 1)
        os_ << ", ";
    }
    os_ << " ]";
  }

  /** Visit a bit-vector extract */
  void visit(const SymBitVectorExtract * const bv) {
    (*this)(bv->bv_);
    os_ << "[" << std::dec << bv->high_bit_ << ":" << bv->low_bit_ << "]";
  }

  /** Visit a bit-vector function */
  void visit(const SymBitVectorFunction * const bv) {
    os_ << bv->f_.name << "(";

    for(size_t i = 0; i < bv->args_.size(); ++i) {
      (*this)(bv->args_[i]);
      if (i != bv->args_.size() - 1)
        os_ << ", ";
    }

    os_ << ")";
  }

  /** Visit a bit-vector if-then-else */
  void visit(const SymBitVectorIte * const bv) {
    os_ << "(if ";
    (*this)(bv->cond_);
    os_ << " then ";
    (*this)(bv->a_);
    os_ << " else ";
    (*this)(bv->b_);
    os_ << ")";
  }

  /** Visit a bit-vector sign-extend */
  void visit(const SymBitVectorSignExtend * const bv) {
    os_ << "(sign-extend-" << bv->size_ << " ";
    (*this)(bv->bv_);
    os_ << ")";
  }

  /** Visit a bit-vector variable */
  void visit(const SymBitVectorVar * const bv) {
    os_ << "<" << bv->name_ << "|" << bv->size_ << ">";
  }

  /** Visit a boolean FALSE */
  void visit(const SymBoolFalse * const b) {
    os_ << "FALSE";
  }

  /** Visit a boolean NOT */
  void visit(const SymBoolNot * const b) {
    os_ << "(not ";
    (*this)(b->b_);
    os_ << ")";
  }

  /** Visit a boolean TRUE */
  void visit(const SymBoolTrue * const b) {
    os_ << "TRUE";
  }

  /** Visit a boolean VAR */
  void visit(const SymBoolVar * const b) {
    os_ << "<" << b->name_ << ">";
  }

private:
  std::ostream& os_;

};

} //namespace

#endif