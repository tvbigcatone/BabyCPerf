/* ir_lin_light.c — extract from ir_lower.c (light window + self-call). */
#include "ir_lin_light.h"
#include "ir_lin_tabs.h"
#include "ir_lin.h"
#include "ir_runtime.h"
#include "interpreter.h"
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* Provided by ir_lower.c */
void Step(const IrLinInst *In, long long *R, long long *Locals, int NLocals, int *Ip);
extern struct ParseState *LinParser;
int IrVmStrictOn(void);
extern unsigned char LinRegU[IR_LIN_REGS];
int LinExecIndexCopy(const IrLinInst *In, long long *R, long long *Locals, int NLocals, int *Ip);
int IrKernelStmtScalarOnly(IrStmt *S, int depth);

long long LightParam[LIGHT_MAX][IR_CALL_MAX_PARAMS];
long long LightLocal[LIGHT_MAX][LIGHT_LOCALS];
unsigned long long LightInitMask[LIGHT_MAX];
int LightSp;

int IrFnCodeHasPtrSlots(FnCodeSlot *CS)
{
    /* LightFrameSafe already proved the body never forms a local address
     * or mutates parent-frame storage. STRICT must not veto that window:
     * doing so forced a full IrCallFrame on every scalar leaf (call_loop). */
    if (CS == NULL) return 0;
    return CS->HasPtrSlots != 0;
}

long long LightRunBody(FnCodeSlot *CS, int lsp);
int IrTryKernelForLight(IrStmt *S, long long *LLoc, long long *LParam, int nloc, int nparam, int param_bound_hint);

/* Light-path mono + memo: close VM↔IR gap on pure recursive leaves. */
long long LightCallSelf(FnCodeSlot *CS, struct Value *FV,
                               long long *args, int na,
                               const unsigned char *ArgTypeBase)
{
    long long hit, res;
    int nsp, ai;
    if (FV == NULL || CS == NULL)
        return 0;
    /* 1) Specialized mono (fib/fact/…) — matches Body-IR speed. */
    if (CS->MonoElig == 1 && na >= 1 && na <= 2)
        return IrMonoRun(FV, args, na);
    /* 2) Memo hit. */
    if (CS->MemoElig == 1 && na >= 1
        && IrMemoLookup(FV, args, na, &hit))
        return hit;
    /* 3) Interpret light body. */
    if (LightSp >= LIGHT_MAX)
        return 0;
    nsp = LightSp;
    IrLightCopyArgs(FV, args, na, LightParam[nsp], ArgTypeBase);
    LightInitMask[nsp] = 0ULL;
    LightSp = nsp + 1;
    if (IdxN > 0 || IdxDirty)
    {
        IdxRunSave irs;
        IdxRunPush(&irs);
        res = LightRunBody(CS, nsp);
        IdxRunPop(&irs);
    }
    else
        res = LightRunBody(CS, nsp);
    LightSp = nsp;
    if (CS->MemoElig == 1 && na >= 1)
        IrMemoStore(FV, args, na, res);
    return res;
}


/* Scalar for-loop on light windows (fib-style). Bound from param/local. */
int IrTryKernelForLight(IrStmt *S, long long *LLoc, long long *LParam,
                               int nloc, int nparam, int param_bound_hint)
{
    long long bound, iv, start;
    int iSlot;
    enum LexToken Op;
    if (S == NULL || S->Kind != IrStFor || LLoc == NULL)
        return 0;
    if (!S->FastCond.Active || !S->FastInc.Active)
        return 0;
    if (S->BodyStmt == NULL || !IrKernelStmtScalarOnly(S->BodyStmt, 0))
        return 0;
    iSlot = S->FastInc.VarSlot;
    if (iSlot < 0 && S->FastCond.VarSlot >= 0)
        iSlot = S->FastCond.VarSlot;
    if (iSlot < 0 || iSlot >= nloc)
        return 0;
    Op = S->FastCond.Op;
    if (!S->FastCond.BoundIsVar)
        bound = S->FastCond.Bound;
    else if (param_bound_hint > 0 && param_bound_hint <= nparam && LParam)
        bound = LParam[param_bound_hint - 1];
    else if (S->FastCond.BoundSlot >= 0 && S->FastCond.BoundSlot < nloc)
        bound = LLoc[S->FastCond.BoundSlot];
    else if (S->FastCond.BoundSlot >= 0 && S->FastCond.BoundSlot < nparam && LParam)
        bound = LParam[S->FastCond.BoundSlot];
    else if (S->FastCond.BoundIsVar && LParam && nparam >= 1
             && S->FastCond.BoundSlot < 0)
        /* BoundSlot often -1 for params; first formal is the common case (fib). */
        bound = LParam[0];
    else
        return 0;
    if (Op == TokenLessEqual) bound += 1;
    else if (Op != TokenLessThan) return 0;
    if (bound < 0 || bound > 100000000LL) return 0;
    start = LLoc[iSlot];
    for (iv = start; iv < bound; iv++)
    {
        IrStmt *B = S->BodyStmt;
        IrStmt *list[16];
        int bn = 0, bi;
        LLoc[iSlot] = iv;
        if (B->Kind == IrStBlock)
        {
            for (bi = 0; bi < B->StmtCount && bn < 16; bi++)
                list[bn++] = B->Stmts[bi];
        }
        else
            list[bn++] = B;
        for (bi = 0; bi < bn; bi++)
        {
            IrStmt *St = list[bi];
            IrExpr *E, *D, *R;
            long long Rv;
            if (St == NULL || St->Kind != IrStExpr || St->Expr == NULL)
                return 0;
            E = St->Expr;
            if (E->Kind != IrExAssign || E->Left == NULL || E->Right == NULL)
                return 0;
            D = E->Left;
            if (D->Kind != IrExIdent || D->LocalSlot < 0 || D->LocalSlot >= nloc)
                return 0;
            R = E->Right;
            if (R->Kind == IrExConst)
                Rv = R->ConstVal;
            else if (R->Kind == IrExIdent)
            {
                if (R->LocalSlot >= 0 && R->LocalSlot < nloc)
                    Rv = LLoc[R->LocalSlot];
                else if (R->ParamSlot >= 0 && R->ParamSlot < nparam && LParam)
                    Rv = LParam[R->ParamSlot];
                else
                    return 0;
            }
            else if (R->Kind == IrExBinOp && R->Left && R->Right)
            {
                long long a, b;
                if (R->Left->Kind == IrExConst) a = R->Left->ConstVal;
                else if (R->Left->Kind == IrExIdent && R->Left->LocalSlot >= 0
                         && R->Left->LocalSlot < nloc)
                    a = LLoc[R->Left->LocalSlot];
                else if (R->Left->Kind == IrExIdent && R->Left->ParamSlot >= 0
                         && R->Left->ParamSlot < nparam && LParam)
                    a = LParam[R->Left->ParamSlot];
                else return 0;
                if (R->Right->Kind == IrExConst) b = R->Right->ConstVal;
                else if (R->Right->Kind == IrExIdent && R->Right->LocalSlot >= 0
                         && R->Right->LocalSlot < nloc)
                    b = LLoc[R->Right->LocalSlot];
                else if (R->Right->Kind == IrExIdent && R->Right->ParamSlot >= 0
                         && R->Right->ParamSlot < nparam && LParam)
                    b = LParam[R->Right->ParamSlot];
                else return 0;
                switch (R->Op)
                {
                    case TokenPlus: Rv = (long long)((unsigned long long)a + (unsigned long long)b); break;
                    case TokenMinus: Rv = (long long)((unsigned long long)a - (unsigned long long)b); break;
                    case TokenAsterisk: Rv = (long long)((unsigned long long)a * (unsigned long long)b); break;
                    default: return 0;
                }
            }
            else
                return 0;
            LLoc[D->LocalSlot] = Rv;
        }
    }
    LLoc[iSlot] = iv;
    return 1;
}

#if defined(_MSC_VER)
#define BABYC_LIGHT_WIDE_NOINLINE __declspec(noinline)
#else
#define BABYC_LIGHT_WIDE_NOINLINE __attribute__((noinline))
#endif
static BABYC_LIGHT_WIDE_NOINLINE long long IrLightWideImmediate(FnCodeSlot *CS, int index, long long fallback)
{
    if (CS == NULL || index < 0 || index >= IR_LIN_STMT_MAX) return fallback;
#ifdef BABYC_FNCODE_PROFILE
    FnCodeProfileRead(FNCODE_P_WIDE);
#endif
    if (CS->WideOn[index])
    {
#ifdef BABYC_FNCODE_PROFILE
        FnCodeProfileRead(FNCODE_P_WIDE);
#endif
        return CS->WideImm[index];
    }
    return fallback;
}

long long LightRunBody(FnCodeSlot *CS, int lsp)
{
    long long LR[IR_LIN_REGS];
    long long *LLoc;
    const IrLinInst *C;
    int nloc, nn, ip, steps, gi;
    long long local_ret = 0;
    if (CS == NULL || CS->N <= 0)
        return 0;
    nloc = CS->MaxLocal > 0 ? CS->MaxLocal : 1;
    LLoc = LightLocal[lsp];
    /* Params live in LightParam[lsp]; only clear true locals. */
    if (CS->MaxLocal > 0)
    {
        for (gi = 0; gi < nloc && gi < LIGHT_LOCALS; gi++)
            LLoc[gi] = 0;
    }
    C = CS->Code;
    nn = CS->N;
    ip = 0;
    steps = 0;
    {
#if defined(__GNUC__) && !defined(BABYC_LIGHT_SWITCH)
        static void *const jt[] = {
            [0] = &&L_default,
            [IrLinImm] = &&L_Imm,
            [IrLinLoadLocal] = &&L_LoadLocal,
            [IrLinStoreLocal] = &&L_StoreLocal,
            [IrLinBin] = &&L_Bin,
            [IrLinUnary] = &&L_Unary,
            [IrLinJmp] = &&L_Jmp,
            [IrLinBrZ] = &&L_BrZ,
            [IrLinBrCmp] = &&L_BrCmp,
            [IrLinRet] = &&L_Ret,
            [IrLinLoadGlobal] = &&L_LoadG,
            [IrLinStoreGlobal] = &&L_StoreG,
            [IrLinLine] = &&L_Line,
            [IrLinCall] = &&L_Call,
            [IrLinIncG] = &&L_IncG,
            [IrLinAddI] = &&L_AddI,
            [IrLinAddLocal] = &&L_AddLocal,
            [IrLinAddStoreLocal] = &&L_AddStoreLocal,
            [IrLinCopyIndex] = &&L_CopyIndex,
        };
#define LIGHT_NEXT() do { \
    if (++steps >= 500000000) goto L_done; \
    if (ip < 0 || ip >= nn) goto L_done; \
    { unsigned op = (unsigned)C[ip].Op; \
      goto *(op < (unsigned)(sizeof(jt)/sizeof(jt[0])) && jt[op] ? jt[op] : &&L_default); } \
} while (0)
        if (nn > 0)
            goto *jt[(unsigned)C[0].Op < sizeof(jt)/sizeof(jt[0]) && jt[C[0].Op] ? C[0].Op : 0];
        goto L_done;
#else
        /* Portable dispatch (MSVC/clang-cl/other): same handlers, switch+goto instead of computed goto. */
#define LIGHT_NEXT() goto L_dispatch
        if (nn <= 0)
            goto L_done;
        L_dispatch:
        if (ip < 0 || ip >= nn || ++steps >= 500000000)
            goto L_done;
        switch ((unsigned)C[ip].Op)
        {
        case IrLinImm: goto L_Imm;
        case IrLinLoadLocal: goto L_LoadLocal;
        case IrLinStoreLocal: goto L_StoreLocal;
        case IrLinBin: goto L_Bin;
        case IrLinUnary: goto L_Unary;
        case IrLinJmp: goto L_Jmp;
        case IrLinBrZ: goto L_BrZ;
        case IrLinBrCmp: goto L_BrCmp;
        case IrLinRet: goto L_Ret;
        case IrLinLoadGlobal: goto L_LoadG;
        case IrLinStoreGlobal: goto L_StoreG;
        case IrLinLine: goto L_Line;
        case IrLinCall: goto L_Call;
        case IrLinIncG: goto L_IncG;
        case IrLinAddI: goto L_AddI;
        case IrLinAddLocal: goto L_AddLocal;
        case IrLinAddStoreLocal: goto L_AddStoreLocal;
        case IrLinCopyIndex: goto L_CopyIndex;
        default: goto L_default;
        }
#endif
        L_Imm: {
            const IrLinInst *In = &C[ip];
            if ((In->Tok == 2 || In->Tok == 3) && In->Imm >= 0
                && In->Imm < IR_LIN_STMT_MAX)
                LR[In->Dest] = CS->WideDirect
                    ? IrLightWideImmediate(CS, (int)In->Imm, In->Imm)
                    : (FNCODE_PROFILE_READ(FNCODE_P_WIDE, LinWideOn[In->Imm])
                        ? FNCODE_PROFILE_READ(FNCODE_P_WIDE, LinWideImm[In->Imm]) : In->Imm);
            else if (In->Tok == 4 && In->Imm >= 0 && In->Imm < nloc && LLoc != NULL)
                LR[In->Dest] = (long long)(uintptr_t)&LLoc[In->Imm];
            else
                LR[In->Dest] = In->Imm;
            ip++; LIGHT_NEXT();
        }
        L_LoadLocal: {
            const IrLinInst *In = &C[ip];
            if (In->Imm >= 0 && In->Imm < 64 && IrUninitChecksOn() && LinParser)
            {
                int slot = (int)In->Imm;
                int uninit = 0;
                /* Light window owns init bitmask when active */
                if (LightSp > 0)
                {
                    /* Owned blob: address is valid after DECL even if the
                     * value map is still empty (matches non-Light LocalOwned). */
                    if (IrCallDepth > 0 && slot < IR_CALL_MAX_LOCALS
                        && IrCallStack[IrCallDepth - 1]->LocalOwned[slot])
                        uninit = 0;
                    else if ((LightInitMask[LightSp - 1] & (1ULL << slot)) == 0)
                        uninit = 1;
                }
                else if (IrCallDepth > 0 && slot < IR_CALL_MAX_LOCALS)
                {
                    IrCallFrame *Fr = IrCallStack[IrCallDepth - 1];
                    if (!Fr->LocalIsPtr[slot] && Fr->LocalArraySize[slot] <= 0
                        && !Fr->LocalOwned[slot]
                        && !Fr->LocalInit[slot])
                        uninit = 1;
                }
                if (uninit)
                {
                    const char *nm = (IrCallDepth > 0 && slot < IR_CALL_MAX_LOCALS)
                        ? IrCallStack[IrCallDepth - 1]->LocalName[slot] : NULL;
                    if (nm) ParserSetCaretOnIdent(LinParser, nm);
                    if (nm && LinParser->SourceText) {
                        const char *s = LinParser->SourceText, *lp;
                        int line = 1, lastline = 1, Nlen = (int)strlen(nm);
                        for (lp = s; *lp; lp++) {
                            if (*lp == '\n') { line++; continue; }
                            if (strncmp(lp, nm, (size_t)Nlen) == 0) {
                                char b = (lp > s) ? lp[-1] : ' ';
                                char a = lp[Nlen];
                                int okb = !((b>='a'&&b<='z')||(b>='A'&&b<='Z')||b=='_'||(b>='0'&&b<='9'));
                                int oka = !((a>='a'&&a<='z')||(a>='A'&&a<='Z')||a=='_'||(a>='0'&&a<='9'));
                                if (okb && oka) lastline = line;
                            }
                        }
                        LinParser->Line = lastline;
                    }
                    if (nm) ParserSetCaretOnIdent(LinParser, nm);
                    ProgramFail(LinParser, DiagnosticMsgUninitializedVariableNamed, nm ? nm : "?");
                }
            }
            if (In->Imm < 0) {
                int ps = (int)(-(In->Imm + 1));
                LR[In->Dest] = (ps >= 0 && ps < IR_CALL_MAX_PARAMS)
                    ? LightParam[lsp][ps] : 0;
            } else if (In->Imm >= 0 && In->Imm < nloc)
                LR[In->Dest] = LLoc[In->Imm];
            else LR[In->Dest] = 0;
            ip++; LIGHT_NEXT();
        }
        L_StoreLocal: {
            const IrLinInst *In = &C[ip];
            if (In->Imm >= 0 && In->Imm < IR_CALL_MAX_LOCALS
                && IrCallDepth > 0
                && IrCallStack[IrCallDepth - 1]->LocalIsConst[In->Imm]
                && LinParser != NULL)
                IrFailReadOnlyAssign(LinParser, 0, 0);
            if (In->Imm < 0) {
                int ps = (int)(-(In->Imm + 1));
                if (ps >= 0 && ps < IR_CALL_MAX_PARAMS)
                    LightParam[lsp][ps] = LR[In->A];
            } else if (In->Imm >= 0 && In->Imm < nloc) {
                long long nv = LR[In->A];
                LLoc[In->Imm] = nv;
                if (In->Imm < 64)
                    LightInitMask[lsp] |= (1ULL << (int)In->Imm);
                /* LightRunBody owns LLoc/LightInitMask for this callee and
                 * has no IrCallFrame of its own. IrCallStack top therefore
                 * belongs to the caller: do not write through to its LocalInit
                 * (nor LocalVal), or a callee store can mask an uninitialised
                 * caller local after the light window returns. */
            }
            ip++; LIGHT_NEXT();
        }
        L_Bin: {
            const IrLinInst *In = &C[ip];
            long long a = LR[In->A], b = LR[In->B], r = 0;
            if (In->Imm & IR_LIN_F_FP) {
                union { long long l; double d; } xa, xb, xr;
                xa.l = a; xb.l = b;
                if (In->Tok == TokenPlus) xr.d = xa.d + xb.d;
                else if (In->Tok == TokenMinus) xr.d = xa.d - xb.d;
                else if (In->Tok == TokenAsterisk) xr.d = xa.d * xb.d;
                else if (In->Tok == TokenSlash)
                    xr.d = (xb.d != 0.0) ? (xa.d / xb.d) : 0.0;
                else xr.l = 0;
                LR[In->Dest] = xr.l; ip++; LIGHT_NEXT();
            }
            switch (In->Tok) {
            case TokenPlus: r = (long long)((unsigned long long)a + (unsigned long long)b); break;
            case TokenMinus: r = (long long)((unsigned long long)a - (unsigned long long)b); break;
            case TokenAsterisk: r = (long long)((unsigned long long)a * (unsigned long long)b); break;
            case TokenSlash: r = b ? a / b : 0; break;
            case TokenModulus: r = b ? a % b : 0; break;
            case TokenEqual: r = (a == b); break;
            case TokenNotEqual: r = (a != b); break;
            case TokenLessThan: r = (a < b); break;
            case TokenGreaterThan: r = (a > b); break;
            case TokenLessEqual: r = (a <= b); break;
            case TokenGreaterEqual: r = (a >= b); break;
            case TokenAmpersand: r = a & b; break;
            case TokenArithmeticOr: r = a | b; break;
            case TokenArithmeticExor: r = a ^ b; break;
            case TokenShiftLeft:
                if (In->Imm & IR_LIN_F_UNSIGNED)
                    r = (long long)((unsigned long long)a << (unsigned)(b & 63));
                else r = a << (b & 63);
                break;
            case TokenShiftRight:
                if (In->Imm & IR_LIN_F_UNSIGNED)
                    r = (long long)((unsigned long long)a >> (unsigned)(b & 63));
                else r = a >> (b & 63);
                break;
            default: r = 0; break;
            }
            LR[In->Dest] = r; ip++; LIGHT_NEXT();
        }
        L_Unary: {
            const IrLinInst *In = &C[ip];
            if (In->Tok == TokenMinus) {
                long long v;
                if (In->Imm & IR_LIN_F_FP) {
                    union { long long l; double d; } u; u.l = LR[In->A]; u.d = -u.d;
                    LR[In->Dest] = u.l;
                } else {
                v = -LR[In->A];
                if (In->Imm & 2) LR[In->Dest] = v;
                else if (In->Imm & 1) LR[In->Dest] = (long long)(unsigned int)v;
                else LR[In->Dest] = (long long)(int)v;
                }
            }
            else if (In->Tok == TokenUnaryNot) LR[In->Dest] = !LR[In->A];
            else if (In->Tok == TokenUnaryExor) {
                long long v = ~LR[In->A];
                if (In->Imm & 2) LR[In->Dest] = v;
                else if (In->Imm & 1) LR[In->Dest] = (long long)(unsigned int)v;
                else LR[In->Dest] = (long long)(int)v;
            }
            else if (In->Tok == TokenCast && In->Imm == 1) {
                union { long long l; double d; } u; u.l = LR[In->A];
                LR[In->Dest] = (long long)u.d;
            }
            else if (In->Tok == TokenCast && In->Imm == 2) {
                union { long long l; double d; } u;
                u.d = (double)LR[In->A];
                LR[In->Dest] = u.l;
            }
            else LR[In->Dest] = LR[In->A];
            ip++; LIGHT_NEXT();
        }
        L_BrZ: {
            const IrLinInst *In = &C[ip];
            if (!LR[In->A]) ip = (int)In->Imm; else ip++;
            LIGHT_NEXT();
        }
        L_BrCmp: {
            const IrLinInst *In = &C[ip];
            long long x = LR[In->A], y = LR[In->B];
            int yes = 0;
            if (In->Dest & 1) {
                unsigned long long ux = (unsigned long long)x, uy = (unsigned long long)y;
                switch (In->Tok) {
                case TokenEqual: yes = ux == uy; break;
                case TokenNotEqual: yes = ux != uy; break;
                case TokenLessThan: yes = ux < uy; break;
                case TokenGreaterThan: yes = ux > uy; break;
                case TokenLessEqual: yes = ux <= uy; break;
                case TokenGreaterEqual: yes = ux >= uy; break;
                default: goto L_default;
                }
            } else {
                switch (In->Tok) {
                case TokenEqual: yes = x == y; break;
                case TokenNotEqual: yes = x != y; break;
                case TokenLessThan: yes = x < y; break;
                case TokenGreaterThan: yes = x > y; break;
                case TokenLessEqual: yes = x <= y; break;
                case TokenGreaterEqual: yes = x >= y; break;
                default: goto L_default;
                }
            }
            if (yes) ip = (int)In->Imm; else ip++;
            LIGHT_NEXT();
        }
        L_Jmp: {
            ip = (int)C[ip].Imm;
            LIGHT_NEXT();
        }
        L_Ret: {
            local_ret = LR[C[ip].A];
            goto L_done;
        }
        L_Line: ip++; LIGHT_NEXT();
        L_LoadG: {
            const IrLinInst *In = &C[ip];
            int g = (int)In->Imm;
            if (g >= 0 && g < 32 && GlobRaw[g] != NULL && In->Tok != 1)
                LR[In->Dest] = *GlobRaw[g];
            else {
                struct Value *V = (g >= 0 && g < GlobN) ? FNCODE_PROFILE_READ(FNCODE_P_GLOB, GlobVal[g]) : NULL;
                if (V != NULL && V->Val != NULL
                    && V->Typ != NULL
                    && (V->Typ->Base == TypeArray
                        || V->Typ->Base == TypeStruct
                        || V->Typ->Base == TypeUnion))
                    LR[In->Dest] = (long long)(intptr_t)(void *)V->Val;
                else if (V != NULL && V->Val != NULL && In->Tok == 1
                         && V->Typ != NULL && V->Typ->Base == TypePointer)
                    LR[In->Dest] = (long long)(intptr_t)V->Val->Pointer;
                else
                    LR[In->Dest] = V ? IR_RET_BITS(V) : 0; /* FP: IEEE bits */
            }
            ip++; LIGHT_NEXT();
        }
        L_StoreG: {
            const IrLinInst *In = &C[ip];
            int g = (int)In->Imm;
            if (g >= 0 && g < 32 && GlobRaw[g] != NULL)
                *GlobRaw[g] = LR[In->A];
            else {
                struct Value *V = (g >= 0 && g < GlobN) ? FNCODE_PROFILE_READ(FNCODE_P_GLOB, GlobVal[g]) : NULL;
                if (V && V->Val) {
                    /* Width/encoding of the global's own type (shared with
                     * the Step executor): was an 8-byte LongLong store. */
                    (void)IrValueStoreBits(V, V->Typ ? V->Typ->Base : TypeInt, LR[In->A]);
                    V->IsInitialized = TRUE;
                }
            }
            ip++; LIGHT_NEXT();
        }
        L_IncG: {
            int g = (int)C[ip].Imm;
            if (g >= 0 && g < 32 && GlobRaw[g] != NULL)
                (*GlobRaw[g])++;
            else if (g >= 0 && g < GlobN && FNCODE_PROFILE_READ(FNCODE_P_GLOB, GlobVal[g]) && FNCODE_PROFILE_READ(FNCODE_P_GLOB, GlobVal[g])->Val) {
                struct Value *V = FNCODE_PROFILE_READ(FNCODE_P_GLOB, GlobVal[g]);
                enum BaseType b = V->Typ ? V->Typ->Base : TypeInt;
                if (b == TypeChar || b == TypeUnsignedChar
                    || b == TypeShort || b == TypeUnsignedShort) {
                    long long oldv;
                    switch (b) {
                    case TypeChar: oldv = V->Val->Character; break;
                    case TypeUnsignedChar: oldv = V->Val->UnsignedCharacter; break;
                    case TypeShort: oldv = V->Val->ShortInteger; break;
                    default: oldv = V->Val->UnsignedShortInteger; break;
                    }
                    oldv = IrNarrowToBaseType(b, oldv + 1);
                    switch (b) {
                    case TypeChar: V->Val->Character = (char)oldv; break;
                    case TypeUnsignedChar: V->Val->UnsignedCharacter = (unsigned char)oldv; break;
                    case TypeShort: V->Val->ShortInteger = (short)oldv; break;
                    default: V->Val->UnsignedShortInteger = (unsigned short)oldv; break;
                    }
                } else if (b == TypeLongLong || b == TypeUnsignedLongLong)
                    V->Val->LongLongInteger += 1;
                else if (b == TypeLong || b == TypeUnsignedLong)
                    V->Val->LongInteger += 1;
                else
                    V->Val->Integer += 1;
                V->IsInitialized = TRUE;
            }
            ip++; LIGHT_NEXT();
        }
        L_AddI: {
            const IrLinInst *In = &C[ip];
            LR[In->Dest] = (long long)((unsigned long long)LR[In->A] + (unsigned long long)In->Imm);
            if (In->B == 1) LR[In->Dest] = (long long)(int)LR[In->Dest];
            else if (In->B == 2) LR[In->Dest] = (long long)(unsigned int)LR[In->Dest];
            ip++; LIGHT_NEXT();
        }
        L_CopyIndex: {
            const IrLinInst *In = &C[ip];
            if (!LinExecIndexCopy(In, LR, LLoc, nloc, &ip)) ip++;
            LIGHT_NEXT();
        }
        L_AddStoreLocal: {
            const IrLinInst *In = &C[ip];
            int slot = (int)In->A;
            if (slot >= 0 && slot < 64 && IrUninitChecksOn() && LinParser
                && LightSp > 0 && (LightInitMask[LightSp - 1] & (1ULL << slot)) == 0) {
                const char *nm = (IrCallDepth > 0 && slot < IR_CALL_MAX_LOCALS)
                    ? IrCallStack[IrCallDepth - 1]->LocalName[slot] : NULL;
                if (nm) ParserSetCaretOnIdent(LinParser, nm);
                ProgramFail(LinParser, DiagnosticMsgUninitializedVariableNamed, nm ? nm : "?");
            }
            long long v = (slot >= 0 && slot < nloc ? LLoc[slot] : 0) + LR[In->B];
            if (slot >= 0 && slot < nloc) {
                LLoc[slot] = v;
                if (slot < 64) LightInitMask[lsp] |= (1ULL << slot);
                /* Light window owns init via LightInitMask; do not alias caller. */
            }
            LR[In->Dest] = v;
            if (In->Dest < IR_LIN_REGS) LinRegU[In->Dest] = 0;
            ip++; LIGHT_NEXT();
        }
        L_AddLocal: {
            const IrLinInst *In = &C[ip];
            int s = (int)In->A;
            if (s >= 0 && s < LIGHT_LOCALS && LightSp > 0)
            {
                LightLocal[LightSp - 1][s] += In->Imm;
                if ((int)In->Tok == (int)TypeChar || (int)In->Tok == (int)TypeUnsignedChar
                    || (int)In->Tok == (int)TypeShort || (int)In->Tok == (int)TypeUnsignedShort)
                    LightLocal[LightSp - 1][s] = IrNarrowToBaseType((enum BaseType)In->Tok, LightLocal[LightSp - 1][s]);
                if (s < 64)
                    LightInitMask[LightSp - 1] |= (1ULL << s);
                LR[In->Dest] = LightLocal[LightSp - 1][s];
                if (s < nloc) LLoc[s] = LightLocal[LightSp - 1][s];
            }
            else if (s >= 0 && s < nloc)
            {
                LLoc[s] += In->Imm;
                if ((int)In->Tok == (int)TypeChar || (int)In->Tok == (int)TypeUnsignedChar
                    || (int)In->Tok == (int)TypeShort || (int)In->Tok == (int)TypeUnsignedShort)
                    LLoc[s] = IrNarrowToBaseType((enum BaseType)In->Tok, LLoc[s]);
                LR[In->Dest] = LLoc[s];
            }
            else
                LR[In->Dest] = 0;
            ip++; LIGHT_NEXT();
        }
        L_Call: {
            const IrLinInst *In = &C[ip];
            int ci = (int)In->Imm;
            int na = (ci >= 0 && ci < CallN) ? FNCODE_PROFILE_READ(FNCODE_P_CALL, CallArgN[ci]) : 0;
            struct Value *FV = (ci >= 0 && ci < CallN) ? FNCODE_PROFILE_READ(FNCODE_P_CALL, CallFnTab[ci]) : NULL;
            long long args[IR_LIN_CALL_ARGS];
            int ai;
            for (ai = 0; ai < na && ai < IR_LIN_CALL_ARGS; ai++)
                args[ai] = LR[FNCODE_PROFILE_READ(FNCODE_P_CALL, CallArgReg[ci][ai])];
            if (FV != NULL && CS->Func == FV && LightSp < LIGHT_MAX
                && CS->MaxLocal <= LIGHT_LOCALS && !CS->HasArrayKernel && !IrFnCodeHasPtrSlots(CS))
            {
                LR[In->Dest] = LightCallSelf(CS, FV, args, na,
                    (ci >= 0 && ci < CS->CallN) ? CS->CallArgTypeBase[ci] : NULL);
                ip++; LIGHT_NEXT();
            }
            Step(In, LR, LLoc, nloc, &ip);
            LIGHT_NEXT();
        }
        L_default: {
            Step(&C[ip], LR, LLoc, nloc, &ip);
            LIGHT_NEXT();
        }
        L_done: ;
#undef LIGHT_NEXT
    }
    BabycLinInstExec += (unsigned long long)steps;
    return local_ret;
}

