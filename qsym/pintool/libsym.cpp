#include "libsym.h"
#include "expr.h"

#include <assert.h>
#include <fcntl.h> /* For O_* constants */
#include <grpcpp/grpcpp.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/stat.h> /* For mode constants */
#include <sys/types.h>
#include <unistd.h>


#include "libsym.h"
#include "service.pb.h"
#include "shm_shared.h"

using google::protobuf::Message;
using grpc::ServerContext;
using grpc::Status;

/*
int kindToSymLibKind[qsym::Kind::Invalid] = {
    ExpressionKind::KIND_BOOL,    // Bool,     // 0
    ExpressionKind::KIND_INTEGER, // Constant, // 1
    ExpressionKind::KIND_INTEGER, // Read,     // 2
    ExpressionKind::KIND_INTEGER, // Concat,   // 3
    ExpressionKind::KIND_INTEGER, // Extract,  // 4
    ExpressionKind::KIND_INTEGER, //     ZExt, // 5
    ExpressionKind::KIND_INTEGER, //   SExt, // 6

    //   // Arithmetic
    ExpressionKind::KIND_INTEGER, //   Add, // 7
    ExpressionKind::KIND_INTEGER, //   Sub, // 8
    ExpressionKind::KIND_INTEGER, //   Mul, // 9
    ExpressionKind::KIND_INTEGER, //   UDiv, // 10
    ExpressionKind::KIND_INTEGER, //   SDiv, // 11
    ExpressionKind::KIND_INTEGER, //   URem, // 12
    ExpressionKind::KIND_INTEGER, //   SRem, // 13
    ExpressionKind::KIND_INTEGER, //   Neg,  // 14

    //   // Bit
    ExpressionKind::KIND_INTEGER, //   Not, // 15
    ExpressionKind::KIND_INTEGER, //   And, // 16
    ExpressionKind::KIND_INTEGER, //   Or, // 17
    ExpressionKind::KIND_INTEGER, //   Xor, // 18
    ExpressionKind::KIND_INTEGER, //   Shl, // 19
    ExpressionKind::KIND_INTEGER, //   LShr, // 20
    ExpressionKind::KIND_INTEGER, //   AShr, // 21

    //   // Compare
    ExpressionKind::KIND_BOOL, //   Equal, // 22
    ExpressionKind::KIND_BOOL, //   Distinct, // 23
    ExpressionKind::KIND_BOOL, //   Ult, // 24
    ExpressionKind::KIND_BOOL, //   Ule, // 25
    ExpressionKind::KIND_BOOL, //   Ugt, // 26
    ExpressionKind::KIND_BOOL, //   Uge, // 27
    ExpressionKind::KIND_BOOL, //   Slt, // 28
    ExpressionKind::KIND_BOOL, //   Sle, // 29
    ExpressionKind::KIND_BOOL, //   Sgt, // 30
    ExpressionKind::KIND_BOOL, //   Sge, // 31

    //   // Logical
    ExpressionKind::KIND_BOOL, //   LOr, // 32
    ExpressionKind::KIND_BOOL, //   LAnd, // 33
    ExpressionKind::KIND_BOOL, //   LNot, // 34

    //   // Special
    ExpressionKind::KIND_INTEGER, //   Ite, // 35

    //   // Virtual operation
    ExpressionKind::KIND_INTEGER, //   Rol,
    ExpressionKind::KIND_INTEGER, //   Ror,
    //   Invalid
};

int kindToSymLibType[qsym::Kind::Invalid] = {
    ExpressionType::TYPE_CONCRETE,  // Bool,     // 0
    ExpressionType::TYPE_CONCRETE, // Constant, // 1
    ExpressionType::TYPE_SYMBOLIC, // Read,     // 2
    ExpressionType::TYPE_BINARY, // Concat,   // 3
    ExpressionType::TYPE_BINARY, // Extract,  // 4
    ExpressionType::TYPE_BINARY, //     ZExt, // 5
    ExpressionType::TYPE_BINARY, //   SExt, // 6

    //   // Arithmetic
    ExpressionType::TYPE_BINARY, //   Add, // 7
    ExpressionType::TYPE_BINARY, //   Sub, // 8
    ExpressionType::TYPE_BINARY, //   Mul, // 9
    ExpressionType::TYPE_BINARY, //   UDiv, // 10
    ExpressionType::TYPE_BINARY, //   SDiv, // 11
    ExpressionType::TYPE_BINARY, //   URem, // 12
    ExpressionType::TYPE_BINARY, //   SRem, // 13
    ExpressionType::TYPE_BINARY, //   Neg,  // 14

    //   // Bit
    ExpressionType::TYPE_UNARY, //   Not, // 15
    ExpressionType::TYPE_BINARY, //   And, // 16
    ExpressionType::TYPE_BINARY, //   Or, // 17
    ExpressionType::TYPE_BINARY, //   Xor, // 18
    ExpressionType::TYPE_BINARY, //   Shl, // 19
    ExpressionType::TYPE_BINARY, //   LShr, // 20
    ExpressionType::TYPE_BINARY, //   AShr, // 21

    //   // Compare
    ExpressionType::TYPE_BINARY, //   Equal, // 22
    ExpressionType::TYPE_BINARY, //   Distinct, // 23
    ExpressionType::TYPE_BINARY, //   Ult, // 24
    ExpressionType::TYPE_BINARY, //   Ule, // 25
    ExpressionType::TYPE_BINARY, //   Ugt, // 26
    ExpressionType::TYPE_BINARY, //   Uge, // 27
    ExpressionType::TYPE_BINARY, //   Slt, // 28
    ExpressionType::TYPE_BINARY, //   Sle, // 29
    ExpressionType::TYPE_BINARY, //   Sgt, // 30
    ExpressionType::TYPE_BINARY, //   Sge, // 31

    //   // Logical
    ExpressionType::TYPE_BINARY, //   LOr, // 32
    ExpressionType::TYPE_BINARY, //   LAnd, // 33
    ExpressionType::TYPE_BINARY, //   LNot, // 34

    //   // Special
    ExpressionType::TYPE_TERNARY, //   Ite, // 35

    //   // Virtual operation
    ExpressionType::TYPE_BINARY, //   Rol,
    ExpressionType::TYPE_BINARY, //   Ror,
    //   Invalid
};
*/

ExpressionOp kindToSymLibOp[qsym::Kind::Invalid] = {
    ExpressionOp::OP_INVALID,  // Bool,     // 0
    ExpressionOp::OP_INVALID, // Constant, // 1
    ExpressionOp::OP_INVALID, // Read,     // 2
    ExpressionOp::OP_CONCAT, // Concat,   // 3
    ExpressionOp::OP_EXTRACT, // Extract,  // 4
    ExpressionOp::OP_ZEXT, //     ZExt, // 5
    ExpressionOp::OP_SEXT, //   SExt, // 6

    //   // Arithmetic
    ExpressionOp::OP_ADD, //   Add, // 7
    ExpressionOp::OP_SUB, //   Sub, // 8
    ExpressionOp::OP_MUL, //   Mul, // 9
    ExpressionOp::OP_UDIV, //   UDiv, // 10
    ExpressionOp::OP_SDIV, //   SDiv, // 11
    ExpressionOp::OP_UREM, //   URem, // 12
    ExpressionOp::OP_SREM, //   SRem, // 13
    ExpressionOp::OP_NEG, //   Neg,  // 14

    //   // Bit
    ExpressionOp::OP_NOT, //   Not, // 15
    ExpressionOp::OP_AND, //   And, // 16
    ExpressionOp::OP_OR, //   Or, // 17
    ExpressionOp::OP_XOR, //   Xor, // 18
    ExpressionOp::OP_SHL, //   Shl, // 19
    ExpressionOp::OP_LSHR, //   LShr, // 20
    ExpressionOp::OP_ASHR, //   AShr, // 21

    //   // Compare
    ExpressionOp::OP_EQ, //   Equal, // 22
    ExpressionOp::OP_NEQ, //   Distinct, // 23
    ExpressionOp::OP_ULT, //   Ult, // 24
    ExpressionOp::OP_ULE, //   Ule, // 25
    ExpressionOp::OP_UGT, //   Ugt, // 26
    ExpressionOp::OP_UGE, //   Uge, // 27
    ExpressionOp::OP_SLT, //   Slt, // 28
    ExpressionOp::OP_SLE, //   Sle, // 29
    ExpressionOp::OP_SGT, //   Sgt, // 30
    ExpressionOp::OP_SGE, //   Sge, // 31

    //   // Logical
    ExpressionOp::OP_LOR, //   LOr, // 32
    ExpressionOp::OP_LAND, //   LAnd, // 33
    ExpressionOp::OP_LNOT, //   LNot, // 34

    //   // Special
    ExpressionOp::OP_ITE, //   Ite, // 35

    //   // Virtual operation
    ExpressionOp::OP_INVALID, //   Rol,
    ExpressionOp::OP_INVALID, //   Ror,
    //   Invalid
};

int SymLibOpTokind[ExpressionOp::OP_END + 1] = {
    0, // OP_INVALID      = 0;
    qsym::Kind::Neg, // OP_NEG          = 1;
    qsym::Kind::Not, // OP_NOT          = 2;
    qsym::Kind::LNot, // OP_LNOT         = 3;
    qsym::Kind::Add, // OP_ADD          = 4;
    qsym::Kind::Sub, // OP_SUB          = 5;
    qsym::Kind::Mul, // OP_MUL          = 6;
    qsym::Kind::UDiv, // OP_UDIV         = 7;
    qsym::Kind::SDiv, // OP_SDIV         = 8;
    qsym::Kind::URem, // OP_UREM         = 9;
    qsym::Kind::SRem, // OP_SREM         = 10;
    qsym::Kind::And, // OP_AND          = 11;
    qsym::Kind::LAnd, // OP_LAND         = 12;
    qsym::Kind::Or, // OP_OR           = 13;
    qsym::Kind::LOr, // OP_LOR          = 14;
    qsym::Kind::Xor, // OP_XOR          = 15;
    qsym::Kind::Equal, // OP_EQ           = 16;
    qsym::Kind::Distinct, // OP_NEQ          = 17;
    qsym::Kind::Ugt, // OP_UGT          = 18;
    qsym::Kind::Uge, // OP_UGE          = 19;
    qsym::Kind::Ult, // OP_ULT          = 20;
    qsym::Kind::Ule, // OP_ULE          = 21;
    qsym::Kind::Sgt, // OP_SGT          = 22;
    qsym::Kind::Sge, // OP_SGE          = 23;
    qsym::Kind::Slt, // OP_SLT          = 24;
    qsym::Kind::Sle, // OP_SLE          = 25;
    qsym::Kind::ZExt, // OP_ZEXT         = 26; // binary: expr, addedNumBits
    qsym::Kind::SExt, // OP_SEXT         = 27; // binary: expr, addedNumBits
    qsym::Kind::Shl, // OP_SHL          = 28; // binary: expr, shiftedNumBits
    qsym::Kind::AShr, // OP_ASHR         = 29; // binary: expr, shiftedNumBits
    qsym::Kind::LShr, // OP_LSHR         = 30; // binary: expr, shiftedNumBits
    qsym::Kind::Concat, // OP_CONCAT       = 31;
    qsym::Kind::Ite, // OP_ITE              = 32;
    qsym::Kind::Extract // OP_EXTRACT          = 33;
};

class SymbolicExpressionBuilderServiceStub {

private:
  int fd;
  char *shared;
  sem_t *sem[N_ACTORS * 2] = {nullptr};

  Status execute(FunctionType fnType, const Message *request, Message *reply) {
    // printf("ITERATION\n");
    //
    struct timespec tim;
    tim.tv_sec = 0;
    tim.tv_nsec = 100;
    FunctionType *ft = SHM_FN_PTR(shared, ACTOR_A);
    while (1) {
      sem_wait(sem[2 * ACTOR_A]); /* nobody can access */
      if (*ft == FunctionType::invalidFunctionType)
        break;
      sem_post(sem[2 * ACTOR_A]); /* others can access */
      nanosleep(&tim, NULL);      /* leave time to other actors */
    }
    //
    *ft = fnType;
    //
    int64_t *requester_id = SHM_REQUESTER_PTR(shared, ACTOR_A);
    *requester_id = ACTOR_B;
    //
    int64_t *request_size = SHM_REQUEST_SIZE_PTR(shared, ACTOR_A);
    *request_size = request->ByteSizeLong();
    //
    char *out = SHM_REQUEST_PTR(shared, ACTOR_A);
    request->SerializeToArray(out, *request_size);
    // printf("SUBMITTING: requestSize: %ld\n", *request_size);
    //
    sem_post(sem[2 * ACTOR_A]);     /* others can access */
    sem_post(sem[2 * ACTOR_A + 1]); /* receiver should read */
    //
    sem_wait(sem[2 * ACTOR_B + 1]); /* there is something for me */
    sem_wait(sem[2 * ACTOR_B + 0]); /* nobody is accessing */
    //
    int64_t *reply_size = SHM_REPLY_SIZE_PTR(shared, ACTOR_B);
    out = SHM_REPLY_PTR(shared, ACTOR_B);
    reply->ParseFromString(std::string(out, *reply_size));
    // printf("REPLY_SIZE_OFF: %ld - REPLY_SIZE: %ld\n", ((char*)reply_size) -
    // shared, *reply_size);
    //
    sem_post(sem[2 * ACTOR_B + 0]); /* other can access */

    return Status::OK;
  }

public:
  SymbolicExpressionBuilderServiceStub() {
    struct timespec tim;
    tim.tv_sec = 0;
    tim.tv_nsec = 50;

    for (int i = 0; i < N_ACTORS; i++) {
      char name[32];
      snprintf(name, sizeof(name), "sprc_sem_read_actor_%d", i);
      while ((sem[2 * i] = sem_open(name, 0)) == SEM_FAILED) {
        printf("waiting for the semaphore\n");
        nanosleep(&tim, NULL);
      }
      snprintf(name, sizeof(name), "sprc_sem_write_actor_%d", i);
      while ((sem[2 * i + 1] = sem_open(name, 0)) == SEM_FAILED) {
        printf("waiting for the semaphore\n");
        nanosleep(&tim, NULL);
      }
    }

    if ((fd = shm_open(SHM_NAME, O_RDWR, 0644)) == -1) {
      perror("shm_open");
      exit(1);
    }

    if ((shared = (char *)mmap(NULL, SHM_SIZE, PROT_READ | PROT_WRITE,
                               MAP_SHARED, fd, 0)) == MAP_FAILED) {
      perror("mmap");
      exit(1);
    }

    printf("INIT DONE\n");
  }

  ~SymbolicExpressionBuilderServiceStub() {
    for (int i = 0; i < N_ACTORS; i++) {
      sem_close(sem[2 * i]);
      sem_close(sem[2 * i + 1]);
    }
  }

  Status buildSymbolicIntegerExpression(ServerContext *context,
                                            const IntegerSymbolicValue *request,
                                            ExpressionRef *reply) {
    return execute(buildSymbolicIntegerExpressionType, request, reply);
  }

  Status buildConcreteIntegerExpression(ServerContext *context,
                                        const IntegerConcreteValue *request,
                                        ExpressionRef *reply) {
    return execute(buildConcreteIntegerExpressionType, request, reply);
  }

  Status buildConcreteBoolExpression(ServerContext *context,
                                        const BoolConcreteValue *request,
                                        ExpressionRef *reply) {
    return execute(buildConcreteBoolExpressionType, request, reply);
  }

  Status buildUnaryExpression(ServerContext *context,
                              const DerivedExpressionArgs *request,
                              ExpressionRef *reply) {
    return execute(buildUnaryExpressionType, request, reply);
  }

  Status buildBinaryExpression(ServerContext *context,
                               const DerivedExpressionArgs *request,
                               ExpressionRef *reply) {
    return execute(buildBinaryExpressionType, request, reply);
  }

  Status buildTernaryExpression(ServerContext *context,
                               const DerivedExpressionArgs *request,
                               ExpressionRef *reply) {
    return execute(buildTernaryExpressionType, request, reply);
  }

  Status macroKind(ServerContext *context, const ExpressionRef *request,
               ExpressionMacroKind* reply) {
    return execute(macroKindType, request, reply);
  }

  Status bits(ServerContext *context, const ExpressionRef *request,
               IntegerConcreteValue* reply) {
    return execute(bitsType, request, reply);
  }

  Status hash(ServerContext *context, const ExpressionRef *request,
               ExpressionHash* reply) {
    return execute(hashType, request, reply);
  }

  Status child(ServerContext *context, const ExpressionChild *request,
               ExpressionRef* reply) {
    return execute(childType, request, reply);
  }

  Status symbolicIntegerValue(ServerContext *context, const ExpressionRef *request,
               IntegerSymbolicValue* reply) {
    return execute(symbolicIntegerValueType, request, reply);
  }

  Status concreteIntegerValue(ServerContext *context, const ExpressionRef *request,
               IntegerConcreteValue* reply) {
    return execute(concreteIntegerValueType, request, reply);
  }

  Status concreteBoolValue(ServerContext *context, const ExpressionRef *request,
               BoolConcreteValue* reply) {
    return execute(concreteBoolValueType, request, reply);
  }

  Status depth(ServerContext *context, const ExpressionRef *request,
               IntegerConcreteValue* reply) {
    return execute(depthType, request, reply);
  }

  Status numChildren(ServerContext *context, const ExpressionRef *request,
               IntegerConcreteValue* reply) {
    return execute(numChildrenType, request, reply);
  }

  Status print(ServerContext *context, const ExpressionRef *request,
               StringMessage *reply) {
    return execute(printType, request, reply);
  }
};

static SymbolicExpressionBuilderServiceStub stub;
static std::map<uint64_t, qsym::ExprRef> idToRef;

void* buildConcreteIntegerExpression(qsym::ExprRef ref, uint64_t value, uint32_t bits) {
    IntegerConcreteValue request;
    request.set_value(value);
    request.set_bits(bits);
    ExpressionRef* reply = new ExpressionRef();
    stub.buildConcreteIntegerExpression(nullptr, &request, reply);
    // idToRef[reply->id()] = ref;
    return reply;
}

void* buildConcreteBoolExpression(qsym::ExprRef ref, bool value) {
    BoolConcreteValue request;
    request.set_value(value);
    ExpressionRef* reply = new ExpressionRef();
    stub.buildConcreteBoolExpression(nullptr, &request, reply);
    // idToRef[reply->id()] = ref;
    return reply;
}

void* buildSymbolicIntegerExpression(qsym::ExprRef ref, uint32_t index) {
    IntegerSymbolicValue request;
    request.set_name(std::to_string(index));
    request.set_bits(8);
    ExpressionRef* reply = new ExpressionRef();
    stub.buildSymbolicIntegerExpression(nullptr, &request, reply);
    // idToRef[reply->id()] = ref;
    return reply;
}

void* buildUnaryExpression(qsym::ExprRef ref, int kind, void* first) {
    if (first == nullptr) abort();
    DerivedExpressionArgs request;
    ExpressionOp op = kindToSymLibOp[kind];
    request.set_op(op);
    request.mutable_first()->set_id(((ExpressionRef*) first)->id());
    ExpressionRef* reply = new ExpressionRef();
    stub.buildUnaryExpression(nullptr, &request, reply);
    // idToRef[reply->id()] = ref;
    return reply;
}

void* buildBinaryExpression(qsym::ExprRef ref, int kind, void* first, void* second) {
    if (first == nullptr || second == nullptr) abort();
    DerivedExpressionArgs request;
    ExpressionOp op = kindToSymLibOp[kind];
    request.set_op(op);
    request.mutable_first()->set_id(((ExpressionRef*) first)->id());
    request.mutable_second()->set_id(((ExpressionRef*) second)->id());
    ExpressionRef* reply = new ExpressionRef();
    stub.buildBinaryExpression(nullptr, &request, reply);
    // idToRef[reply->id()] = ref;
    return reply;
}

void* buildTernaryExpression(qsym::ExprRef ref, int kind, void* first, void* second, void* third) {
    if (first == nullptr || second == nullptr || third == nullptr) abort();
    DerivedExpressionArgs request;
    ExpressionOp op = kindToSymLibOp[kind];
    request.set_op(op);
    request.mutable_first()->set_id(((ExpressionRef*) first)->id());
    request.mutable_second()->set_id(((ExpressionRef*) second)->id());
    request.mutable_third()->set_id(((ExpressionRef*) third)->id());
    ExpressionRef* reply = new ExpressionRef();
    stub.buildTernaryExpression(nullptr, &request, reply);
    // idToRef[reply->id()] = ref;
    return reply;
}

int getKind(void* e) {
    if (e == nullptr) abort();
    ExpressionMacroKind reply;
    stub.macroKind(nullptr, (ExpressionRef*)e, &reply);
    if (reply.op() != ExpressionOp::OP_INVALID) {
        return SymLibOpTokind[reply.op()];
    } else {
        if (reply.kind() == ExpressionKind::KIND_BOOL)
            return qsym::Kind::Bool;
        else if (reply.type() == ExpressionType::TYPE_SYMBOLIC)
            return qsym::Kind::Read;
        else if (reply.type() == ExpressionType::TYPE_CONCRETE)
            return qsym::Kind::Constant;
        else
            abort();
    }
}

uint32_t getBits(void* e) {
    if (e == nullptr) abort();
    IntegerConcreteValue reply;
    stub.bits(nullptr, (ExpressionRef*)e, &reply);
    return (uint32_t) reply.value();
}

bool isConcreteExpr(void* e) {
    if (e == nullptr) abort();
    ExpressionMacroKind reply;
    stub.macroKind(nullptr, (ExpressionRef*)e, &reply);
    if (reply.type() == ExpressionType::TYPE_CONCRETE)
        return true;
    return false;
}

uint64_t hashExpr(void* e) {
    if (e == nullptr) abort();
    ExpressionHash reply;
    stub.hash(nullptr, (ExpressionRef*)e, &reply);
    return reply.hash();
}

qsym::ExprRef getChildExpr(void* e, int index) {
    if (e == nullptr) abort();
    ExpressionChild request;
    request.set_id(((ExpressionRef*)e)->id());
    request.set_index(index);
    ExpressionRef reply;
    stub.child(nullptr, &request, &reply);
    // printf("getChildExpr(%ld, %d): %ld\n", request.id(), index, reply.id());
    return idToRef.at(reply.id());
}

int getNumChildExpr(void* e) {
    if (e == nullptr) abort();

    ExpressionMacroKind reply;
    stub.macroKind(nullptr, (ExpressionRef*)e, &reply);

    int num;

    if (reply.op() == ExpressionOp::OP_ZEXT)
        num = 1;
    else if (reply.op() == ExpressionOp::OP_SEXT)
        num = 1;
    else if (reply.op() == ExpressionOp::OP_SHL)
        num = 1;
    else if (reply.op() == ExpressionOp::OP_ASHR)
        num = 1;
    else if (reply.op() == ExpressionOp::OP_LSHR)
        num = 1;
    else if (reply.op() == ExpressionOp::OP_EXTRACT)
        num = 1;
    else {
        if (reply.type() == ExpressionType::TYPE_UNARY)
            num = 1;
        else if (reply.type() == ExpressionType::TYPE_BINARY)
            num = 2;
        else if (reply.type() == ExpressionType::TYPE_TERNARY)
            num = 3;
        else
            num = 0;
    }

    // debug
    /*
    ExpressionRef* request = (ExpressionRef*) e;
    IntegerConcreteValue reply2;
    stub.numChildren(nullptr, request, &reply2);
    if (reply.op() != ExpressionOp::OP_INVALID && num != reply2.value()) {
      printf("WARNING: kind=%ld type=%d num=%d expected_num=%ld\n", getKind(e), reply.type(), num, reply2.value());
    }

    if (num == 0) {
      // printf("kind(%ld): %d type=%d\n", ((ExpressionRef*)e)->id(), getKind(e), reply.type());
    }
    */
   
    // printf("getNumChildExpr(%ld): %d\n", ((ExpressionRef*)e)->id(), num);
    return num;
}

void setShadowExpr(void* expr, qsym::ExprRef ref) {
    ExpressionRef* e = (ExpressionRef*) expr;
    // printf("setShadowExpr(%ld) = %p\n", e->id(), &ref);
    idToRef[e->id()] = ref;
}

uint32_t getReadIndex(void* e) {
    ExpressionRef* request = (ExpressionRef*) e;
    IntegerSymbolicValue reply;
    stub.symbolicIntegerValue(nullptr, request, &reply);
    return atoi(reply.name().c_str());
}

uint64_t getConcreteIntegerValue(void* e) {
    ExpressionRef* request = (ExpressionRef*) e;
    IntegerConcreteValue reply;
    stub.concreteIntegerValue(nullptr, request, &reply);
    return reply.value();
}

uint32_t getExtractIndex(void* e) {
    ExpressionChild request;
    request.set_id(((ExpressionRef*)e)->id());
    request.set_index(1);
    ExpressionRef child;
    stub.child(nullptr, &request, &child);
    return (uint32_t) getConcreteIntegerValue(&child);
}

uint32_t getExtractBits(void* e) {
    ExpressionChild request;
    request.set_id(((ExpressionRef*)e)->id());
    request.set_index(2);
    ExpressionRef child;
    stub.child(nullptr, &request, &child);
    return (uint32_t) getConcreteIntegerValue(&child);
}

bool getBoolValue(void* e) {
    ExpressionRef* request = (ExpressionRef*) e;
    BoolConcreteValue reply;
    stub.concreteBoolValue(nullptr, request, &reply);
    return reply.value();
}

uint32_t getZExtBits(void* e) {
    ExpressionChild request;
    request.set_id(((ExpressionRef*)e)->id());
    request.set_index(1);
    ExpressionRef child;
    stub.child(nullptr, &request, &child);
    return (uint32_t) getConcreteIntegerValue(&child);
}

uint32_t getSExtBits(void* e) {
    return getZExtBits(e);
}

uint32_t getShiftBits(void* e) {
    return getZExtBits(e);
}

int32_t getDepth(void* e) {
    ExpressionRef* request = (ExpressionRef*) e;
    IntegerConcreteValue reply;
    stub.depth(nullptr, request, &reply);
    return (int32_t) reply.value();
}