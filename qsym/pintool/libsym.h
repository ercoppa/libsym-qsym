#ifndef H_LIBSYM
#define H_LIBSYM

#include <cstdint>
#include "shm_shared.h"
#include "expr_sub.h"

void setShadowExpr(void* expr, qsym::ExprRef ref);

void* buildConcreteIntegerExpression(qsym::ExprRef ref, uint64_t value, uint32_t bits);
void* buildConcreteBoolExpression(qsym::ExprRef ref, bool value);
void* buildSymbolicIntegerByteExpression(qsym::ExprRef ref, uint32_t index);
void* buildUnaryExpression(qsym::ExprRef ref, int kind, void* first);
void* buildBinaryExpression(qsym::ExprRef ref, int kind, void* first, void* second);
void* buildTernaryExpression(qsym::ExprRef ref, int kind, void* first, void* second, void* third);

int getKind(void* e);
uint32_t getBits(void* e);
bool isConcreteExpr(void* e);
uint64_t hashExpr(void* e);
qsym::ExprRef getChildExpr(void* e, int index);
int getNumChildExpr(void* e);
uint32_t getReadIndex(void* e);
bool getBoolValue(void* e);
uint32_t getExtractIndex(void* e);
uint32_t getExtractBits(void* e);
uint64_t getConcreteIntegerValue(void* e);
uint32_t getZExtBits(void* e);
uint32_t getSExtBits(void* e);
uint32_t getShiftBits(void* e);
int32_t getDepth(void* e);

#endif