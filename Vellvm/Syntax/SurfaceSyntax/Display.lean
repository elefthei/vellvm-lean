/- LLVM-like goal display from Vellvm's Syntax/SurfaceSyntax.v (see LICENSE.md).
   All source forms are `only printing`: they can omit types, flags and metadata.
   Open `Vellvm.Syntax.SurfaceSyntax.VIR_Notations` to enable the delaborators;
   `set_option pp.notation false` restores the full constructor representation. -/
module

public meta import Lean
public import Vellvm.Syntax.CFG.Types
public import Vellvm.Syntax.DynamicTypes

public section
namespace Vellvm.Syntax.SurfaceSyntax.VIR_Notations
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Syntax.CFG

scoped instance : Coe IRString raw_id := ⟨raw_id.Name⟩
scoped instance : Coe int_ast raw_id := ⟨raw_id.Anon⟩

declare_syntax_cat vir_typ
declare_syntax_cat vir_exp
declare_syntax_cat vir_instr
declare_syntax_cat vir_term
declare_syntax_cat vir_code
declare_syntax_cat vir_phi
declare_syntax_cat vir_phis
declare_syntax_cat vir_idx_list
declare_syntax_cat vir_phi_args
declare_syntax_cat vir_arm_list
declare_syntax_cat vir_label_list
declare_syntax_cat vir_anns
declare_syntax_cat vir_fmf
declare_syntax_cat vir_typ_list
declare_syntax_cat vir_def_list
declare_syntax_cat vir_decl_list
declare_syntax_cat vir_global_list
declare_syntax_cat vir_tle_list
declare_syntax_cat vir_block_list
declare_syntax_cat vir_iidx_list
declare_syntax_cat vir_root

scoped syntax:1024 (name := prefixVirTyp) "%t" ppSpace vir_typ : vir_root
scoped syntax:1024 (name := prefixVirExp) "%e" ppSpace vir_exp : vir_root
scoped syntax:1024 (name := prefixVirInstr) "%i" ppSpace vir_instr : vir_root
scoped syntax:1024 (name := prefixVirTerm) "%T" ppSpace vir_term : vir_root
scoped syntax:1024 (name := prefixVirPhi) "%p" ppSpace vir_phi : vir_root
scoped syntax:1024 (name := groupVirTyp) "(" vir_typ ")" : vir_typ
scoped syntax:1024 (name := escapeVirTyp) "{" term "}" : vir_typ
scoped syntax:1024 (name := typeVariable) ident : vir_typ
scoped syntax:950 (name := viewTypI) &"i" term:1024 : vir_typ
scoped syntax:950 (name := viewTypPtr) &"ptr" : vir_typ
scoped syntax:950 (name := viewTypTYPEPointer) vir_typ:950 "*" : vir_typ
scoped syntax:950 (name := viewTypVoid) &"void" : vir_typ
scoped syntax:950 (name := viewTypHalf) &"half" : vir_typ
scoped syntax:950 (name := viewTypBfloat) &"bfloat" : vir_typ
scoped syntax:950 (name := viewTypFloat) &"float" : vir_typ
scoped syntax:950 (name := viewTypDouble) &"double" : vir_typ
scoped syntax:950 (name := viewTypFp128) &"fp128" : vir_typ
scoped syntax:950 (name := viewTypX86Fp80) &"x86_fp80" : vir_typ
scoped syntax:950 (name := viewTypPpcFp128) &"ppc_fp128" : vir_typ
scoped syntax:950 (name := viewTypIptr) &"iptr" : vir_typ
scoped syntax:950 (name := viewTypLabel) &"label" : vir_typ
scoped syntax:950 (name := viewTypToken) &"token" : vir_typ
scoped syntax:950 (name := viewTypMetadata) &"metadata" : vir_typ
scoped syntax:950 (name := viewTypOpaque) &"opaque" : vir_typ
scoped syntax:950 (name := viewTypX) "[" term:1024 ppSpace &"x" ppSpace vir_typ "]" : vir_typ
scoped syntax:950 (name := viewTypX2) "<" term:1024 ppSpace &"x" ppSpace vir_typ ">" : vir_typ
scoped syntax:950 (name := viewTyp) "{|" "|}" : vir_typ
scoped syntax:950 (name := viewTyp2) "{|" vir_typ_list "|}" : vir_typ
scoped syntax:950 (name := viewTyp3) "<{" "}>" : vir_typ
scoped syntax:950 (name := viewTyp4) "<{" vir_typ_list "}>" : vir_typ
scoped syntax:920 (name := viewTyp5) vir_typ ppSpace "(" ")" : vir_typ
scoped syntax:920 (name := viewTyp6) vir_typ ppSpace "(" vir_typ_list ")" : vir_typ
scoped syntax:920 (name := viewTyp7) vir_typ ppSpace "(" "..." ")" : vir_typ
scoped syntax:920 (name := viewTyp8) vir_typ ppSpace "(" vir_typ_list "," ppSpace "..." ")" : vir_typ
scoped syntax:950 (name := viewTypTYPEIdentified) "%" term:1024 : vir_typ
scoped syntax:950 (name := viewTypTYPEIdentified2) "@" term:1024 : vir_typ
scoped syntax:1024 (name := groupVirTypList) "(" vir_typ_list ")" : vir_typ_list
scoped syntax:1024 (name := escapeVirTypList) "{" term "}" : vir_typ_list
scoped syntax:1024 (name := groupVirExp) "(" vir_exp ")" : vir_exp
scoped syntax:1024 (name := escapeVirExp) "{" term "}" : vir_exp
scoped syntax:1024 (name := viewExpEXPIdent) "%" term:1024 : vir_exp
scoped syntax:1024 (name := viewExpEXPIdent2) "@" term:1024 : vir_exp
scoped syntax:1024 (name := viewExpEXPInteger) term:1024 : vir_exp
scoped syntax:1024 (name := viewExpNull) &"null" : vir_exp
scoped syntax:1024 (name := viewExpZeroinitializer) &"zeroinitializer" : vir_exp
scoped syntax:1024 (name := viewExpUndef) &"undef" : vir_exp
scoped syntax:1024 (name := viewExpPoison) &"poison" : vir_exp
scoped syntax:1024 (name := viewExpFp) &"fp" ppSpace term:1024 : vir_exp
scoped syntax:1024 (name := viewExpMeta) &"meta" ppSpace term:1024 : vir_exp
scoped syntax:950 (name := viewExpSplat) &"splat" ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:1024 (name := viewExpBlockaddress) &"blockaddress" ppSpace "(" term:1024 "," ppSpace term:1024 ")" : vir_exp
scoped syntax:1024 (name := viewExpTrue) &"true" : vir_exp
scoped syntax:1024 (name := viewExpFalse) &"false" : vir_exp
scoped syntax:1024 (name := viewExpC) &"c" ppSpace "[" vir_idx_list "]" : vir_exp
scoped syntax:1024 (name := viewExp) "{|" vir_idx_list "|}" : vir_exp
scoped syntax:1024 (name := viewExp2) "<{" vir_idx_list "}>" : vir_exp
scoped syntax:1024 (name := viewExp3) "[" vir_idx_list "]" : vir_exp
scoped syntax:1024 (name := viewExp4) "<" vir_idx_list ">" : vir_exp
scoped syntax:930 (name := viewExpAdd) &"add" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpAddNuw) &"add" ppSpace &"nuw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpAddNsw) &"add" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpAddNuwNsw) &"add" ppSpace &"nuw" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpSub) &"sub" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpSubNuw) &"sub" ppSpace &"nuw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpSubNsw) &"sub" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpSubNuwNsw) &"sub" ppSpace &"nuw" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpMul) &"mul" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpMulNuw) &"mul" ppSpace &"nuw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpMulNsw) &"mul" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpMulNuwNsw) &"mul" ppSpace &"nuw" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpShl) &"shl" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpShlNuw) &"shl" ppSpace &"nuw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpShlNsw) &"shl" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpShlNuwNsw) &"shl" ppSpace &"nuw" ppSpace &"nsw" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpUdiv) &"udiv" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpUdivExact) &"udiv" ppSpace &"exact" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpSdiv) &"sdiv" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpSdivExact) &"sdiv" ppSpace &"exact" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpLshr) &"lshr" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpLshrExact) &"lshr" ppSpace &"exact" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpAshr) &"ashr" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpAshrExact) &"ashr" ppSpace &"exact" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpUrem) &"urem" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpSrem) &"srem" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpAnd) &"and" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpOr) &"or" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpOrDisjoint) &"or" ppSpace &"disjoint" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpXor) &"xor" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpEq) &"icmp" ppSpace &"eq" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpNe) &"icmp" ppSpace &"ne" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpUgt) &"icmp" ppSpace &"ugt" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpUge) &"icmp" ppSpace &"uge" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpUlt) &"icmp" ppSpace &"ult" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpUle) &"icmp" ppSpace &"ule" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpSgt) &"icmp" ppSpace &"sgt" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpSge) &"icmp" ppSpace &"sge" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpSlt) &"icmp" ppSpace &"slt" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpIcmpSle) &"icmp" ppSpace &"sle" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFadd) &"fadd" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFsub) &"fsub" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFmul) &"fmul" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFdiv) &"fdiv" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFrem) &"frem" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpFalse) &"fcmp" ppSpace &"false" : vir_exp
scoped syntax:930 (name := viewExpFcmpTrue) &"fcmp" ppSpace &"true" : vir_exp
scoped syntax:930 (name := viewExpFcmpOeq) &"fcmp" ppSpace &"oeq" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpOgt) &"fcmp" ppSpace &"ogt" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpOge) &"fcmp" ppSpace &"oge" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpOlt) &"fcmp" ppSpace &"olt" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpOle) &"fcmp" ppSpace &"ole" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpOne) &"fcmp" ppSpace &"one" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpOrd) &"fcmp" ppSpace &"ord" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpUno) &"fcmp" ppSpace &"uno" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpUeq) &"fcmp" ppSpace &"ueq" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpUgt) &"fcmp" ppSpace &"ugt" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpUge) &"fcmp" ppSpace &"uge" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpUlt) &"fcmp" ppSpace &"ult" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpUle) &"fcmp" ppSpace &"ule" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFcmpUne) &"fcmp" ppSpace &"une" ppSpace vir_exp "," ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpTruncTo) &"trunc" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpTruncNuwTo) &"trunc" ppSpace &"nuw" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpTruncNswTo) &"trunc" ppSpace &"nsw" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpTruncNuwNswTo) &"trunc" ppSpace &"nuw" ppSpace &"nsw" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpZextTo) &"zext" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpZextNnegTo) &"zext" ppSpace &"nneg" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpSextTo) &"sext" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpFptruncTo) &"fptrunc" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpFptruncTo2) &"fptrunc" ppSpace "[" vir_fmf "]" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpFpextTo) &"fpext" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpFpextTo2) &"fpext" ppSpace "[" vir_fmf "]" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpUitofpTo) &"uitofp" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpUitofpNnegTo) &"uitofp" ppSpace &"nneg" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpSitofpTo) &"sitofp" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpFptouiTo) &"fptoui" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpFptosiTo) &"fptosi" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpInttoptrTo) &"inttoptr" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpPtrtointTo) &"ptrtoint" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpPtrtoaddrTo) &"ptrtoaddr" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpBitcastTo) &"bitcast" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpAddrspacecastTo) &"addrspacecast" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace vir_typ : vir_exp
scoped syntax:930 (name := viewExpSelect) &"select" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpGetelementptr) &"getelementptr" ppSpace vir_typ "," ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_idx_list : vir_exp
scoped syntax:930 (name := viewExpExtractelement) &"extractelement" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpInsertelement) &"insertelement" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpShufflevector) &"shufflevector" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpExtractvalue) &"extractvalue" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_iidx_list : vir_exp
scoped syntax:930 (name := viewExpInsertvalue) &"insertvalue" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_iidx_list : vir_exp
scoped syntax:930 (name := viewExpFneg) &"fneg" ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFneg2) &"fneg" ppSpace "[" vir_fmf "]" ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:930 (name := viewExpFreeze) &"freeze" ppSpace vir_typ ppSpace vir_exp : vir_exp
scoped syntax:1024 (name := groupVirInstr) "(" vir_instr ")" : vir_instr
scoped syntax:1024 (name := escapeVirInstr) "{" term "}" : vir_instr
scoped syntax:920 (name := viewInstrProdMk) term:1024 ppSpace "=" ppSpace vir_exp : vir_instr
scoped syntax:920 (name := viewInstrCall) term:1024 ppSpace "=" ppSpace &"call" ppSpace term:1024 ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrCall2) &"call" ppSpace term:1024 ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrAlloca) term:1024 ppSpace "=" ppSpace &"alloca" ppSpace vir_typ : vir_instr
scoped syntax:920 (name := viewInstrAllocaAlign) term:1024 ppSpace "=" ppSpace &"alloca" ppSpace vir_typ "," ppSpace &"align" ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrAlloca2) term:1024 ppSpace "=" ppSpace &"alloca" ppSpace vir_typ "," ppSpace vir_anns : vir_instr
scoped syntax:920 (name := viewInstrLoad) term:1024 ppSpace "=" ppSpace &"load" ppSpace vir_typ "," ppSpace vir_typ ppSpace vir_exp : vir_instr
scoped syntax:920 (name := viewInstrLoadAlign) term:1024 ppSpace "=" ppSpace &"load" ppSpace vir_typ "," ppSpace vir_typ ppSpace vir_exp "," ppSpace &"align" ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrLoadVolatile) term:1024 ppSpace "=" ppSpace &"load" ppSpace &"volatile" ppSpace vir_typ "," ppSpace vir_typ ppSpace vir_exp : vir_instr
scoped syntax:920 (name := viewInstrLoad2) term:1024 ppSpace "=" ppSpace &"load" ppSpace vir_typ "," ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_anns : vir_instr
scoped syntax:920 (name := viewInstrStore) &"store" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp : vir_instr
scoped syntax:920 (name := viewInstrStoreAlign) &"store" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp "," ppSpace &"align" ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrStoreVolatile) &"store" ppSpace &"volatile" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp : vir_instr
scoped syntax:920 (name := viewInstrStore2) &"store" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_anns : vir_instr
scoped syntax:920 (name := viewInstrComment) "#comment" ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrFence) &"fence" ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrCmpxchg) term:1024 ppSpace "=" ppSpace &"cmpxchg" ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrAtomicrmw) term:1024 ppSpace "=" ppSpace &"atomicrmw" ppSpace term:1024 : vir_instr
scoped syntax:920 (name := viewInstrVaArg) term:1024 ppSpace "=" ppSpace &"va_arg" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_typ : vir_instr
scoped syntax:920 (name := viewInstrLandingpad) term:1024 ppSpace "=" ppSpace &"landingpad" ppSpace vir_typ : vir_instr
scoped syntax:1024 (name := groupVirTerm) "(" vir_term ")" : vir_term
scoped syntax:1024 (name := escapeVirTerm) "{" term "}" : vir_term
scoped syntax:920 (name := viewTermRet) &"ret" ppSpace vir_typ ppSpace vir_exp : vir_term
scoped syntax:920 (name := viewTermRetVoid) &"ret" ppSpace &"void" : vir_term
scoped syntax:920 (name := viewTermBrLabelLabel) &"br" ppSpace vir_typ ppSpace vir_exp "," ppSpace &"label" ppSpace term:1024 "," ppSpace &"label" ppSpace term:1024 : vir_term
scoped syntax:920 (name := viewTermBrLabel) &"br" ppSpace &"label" ppSpace term:1024 : vir_term
scoped syntax:920 (name := viewTermUnreachable) &"unreachable" : vir_term
scoped syntax:920 (name := viewTermResume) &"resume" ppSpace vir_typ ppSpace vir_exp : vir_term
scoped syntax:920 (name := viewTermSwitchLabel) &"switch" ppSpace vir_typ ppSpace vir_exp "," ppSpace &"label" ppSpace term:1024 ppSpace vir_arm_list : vir_term
scoped syntax:920 (name := viewTermIndirectbr) &"indirectbr" ppSpace vir_typ ppSpace vir_exp "," ppSpace vir_label_list : vir_term
scoped syntax:920 (name := viewTermInvokeToLabelUnwindLabel) &"invoke" ppSpace vir_typ ppSpace vir_exp ppSpace &"to" ppSpace &"label" ppSpace term:1024 ppSpace &"unwind" ppSpace &"label" ppSpace term:1024 : vir_term
scoped syntax:1024 (name := groupVirCode) "(" vir_code ")" : vir_code
scoped syntax:1024 (name := escapeVirCode) "{" term "}" : vir_code
scoped syntax:1024 (name := groupVirPhi) "(" vir_phi ")" : vir_phi
scoped syntax:1024 (name := escapeVirPhi) "{" term "}" : vir_phi
scoped syntax:920 (name := viewPhiPhi) term:1024 ppSpace "=" ppSpace &"phi" ppSpace vir_typ ppSpace vir_phi_args : vir_phi
scoped syntax:1024 (name := groupVirPhis) "(" vir_phis ")" : vir_phis
scoped syntax:1024 (name := escapeVirPhis) "{" term "}" : vir_phis
scoped syntax:1024 (name := groupVirIdxList) "(" vir_idx_list ")" : vir_idx_list
scoped syntax:1024 (name := escapeVirIdxList) "{" term "}" : vir_idx_list
scoped syntax:950 (name := viewIdxListProdMk) vir_typ ppSpace vir_exp : vir_idx_list
scoped syntax:1024 (name := groupVirPhiArgs) "(" vir_phi_args ")" : vir_phi_args
scoped syntax:1024 (name := escapeVirPhiArgs) "{" term "}" : vir_phi_args
scoped syntax:950 (name := viewPhiArgs) "[" vir_exp "," ppSpace term:1024 "]" : vir_phi_args
scoped syntax:1024 (name := groupVirArmList) "(" vir_arm_list ")" : vir_arm_list
scoped syntax:1024 (name := escapeVirArmList) "{" term "}" : vir_arm_list
scoped syntax:950 (name := viewArmListILabel) vir_typ ppSpace term:max "," ppSpace &"label" ppSpace term:max : vir_arm_list
scoped syntax:1024 (name := groupVirLabelList) "(" vir_label_list ")" : vir_label_list
scoped syntax:1024 (name := escapeVirLabelList) "{" term "}" : vir_label_list
scoped syntax:1024 (name := labelItem) &"label" ppSpace term:1024 : vir_label_list
scoped syntax:1024 (name := groupVirAnns) "(" vir_anns ")" : vir_anns
scoped syntax:1024 (name := escapeVirAnns) "{" term "}" : vir_anns
scoped syntax:950 (name := viewAnnsAlign) &"align" ppSpace term:1024 : vir_anns
scoped syntax:950 (name := viewAnnsVolatile) &"volatile" : vir_anns
scoped syntax:950 (name := viewAnnsAtomic) &"atomic" : vir_anns
scoped syntax:950 (name := viewAnnsInalloca) &"inalloca" : vir_anns
scoped syntax:950 (name := viewAnnsNumElements) &"num_elements" ppSpace vir_typ ppSpace vir_exp : vir_anns
scoped syntax:1024 (name := groupVirFmf) "(" vir_fmf ")" : vir_fmf
scoped syntax:1024 (name := escapeVirFmf) "{" term "}" : vir_fmf
scoped syntax:950 (name := viewFmfNnan) &"nnan" : vir_fmf
scoped syntax:950 (name := viewFmfNinf) &"ninf" : vir_fmf
scoped syntax:950 (name := viewFmfNsz) &"nsz" : vir_fmf
scoped syntax:950 (name := viewFmfArcp) &"arcp" : vir_fmf
scoped syntax:950 (name := viewFmfContract) &"contract" : vir_fmf
scoped syntax:950 (name := viewFmfAfn) &"afn" : vir_fmf
scoped syntax:950 (name := viewFmfReassoc) &"reassoc" : vir_fmf
scoped syntax:950 (name := viewFmfFast) &"fast" : vir_fmf
scoped syntax:940 (name := viewRootFunc) &"func" ppSpace term:1024 ppSpace term:1024 ppSpace ":=" ppLine term:1024 : vir_root
scoped syntax:940 (name := viewRootMkBlock) term:1024 ":" ppLine vir_term : vir_root
scoped syntax:940 (name := viewRootMkBlock2) term:1024 ":" ppLine vir_code ppLine vir_term : vir_root
scoped syntax:940 (name := viewRootMkBlock3) term:1024 ":" ppLine vir_phis ppLine vir_code ppLine vir_term : vir_root
scoped syntax:1024 (name := groupVirDefList) "(" vir_def_list ")" : vir_def_list
scoped syntax:1024 (name := escapeVirDefList) "{" term "}" : vir_def_list
scoped syntax:1024 (name := groupVirDeclList) "(" vir_decl_list ")" : vir_decl_list
scoped syntax:1024 (name := escapeVirDeclList) "{" term "}" : vir_decl_list
scoped syntax:1024 (name := groupVirGlobalList) "(" vir_global_list ")" : vir_global_list
scoped syntax:1024 (name := escapeVirGlobalList) "{" term "}" : vir_global_list
scoped syntax:1024 (name := groupVirIidxList) "(" vir_iidx_list ")" : vir_iidx_list
scoped syntax:1024 (name := escapeVirIidxList) "{" term "}" : vir_iidx_list
scoped syntax:950 (name := viewIidxListZToNumInt) term:1024 : vir_iidx_list
scoped syntax:1024 (name := integerIndex) term:1024 : vir_iidx_list
scoped syntax:1024 (name := groupVirBlockList) "(" vir_block_list ")" : vir_block_list
scoped syntax:1024 (name := escapeVirBlockList) "{" term "}" : vir_block_list
scoped syntax:940 (name := viewRootCfg) &"cfg" ppSpace term:1024 "," ppSpace term:1024 ppSpace "{" ppLine vir_block_list ppLine "}" : vir_root
scoped syntax:940 (name := viewRootModul) &"modul" ppSpace "{" ppLine vir_def_list ppLine "}" : vir_root
scoped syntax:940 (name := viewRootModul2) &"modul" ppSpace "{" ppLine vir_decl_list ppLine "|" ppLine vir_def_list ppLine "}" : vir_root
scoped syntax:940 (name := viewRootGlobal) &"global" ppSpace term:1024 ":" ppSpace vir_typ ppSpace ":=" ppSpace vir_exp : vir_root
scoped syntax:940 (name := viewRootConstant) &"constant" ppSpace term:1024 ":" ppSpace vir_typ ppSpace ":=" ppSpace vir_exp : vir_root
scoped syntax:940 (name := viewRootExtern) &"extern" ppSpace term:1024 ":" ppSpace vir_typ : vir_root
scoped syntax:940 (name := viewRootAlias) &"alias" ppSpace term:1024 ":" ppSpace vir_typ ppSpace ":=" ppSpace vir_exp : vir_root
scoped syntax:940 (name := viewRootDeclare) &"declare" ppSpace term:1024 ":" ppSpace vir_typ : vir_root
scoped syntax:940 (name := viewRootDecl) "#decl" ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootDef) "#def" ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootGlobal2) "#global" ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootType) "#type" ppSpace term:1024 ppSpace ":=" ppSpace vir_typ : vir_root
scoped syntax:940 (name := viewRootTarget) "#target" ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootDatalayout) "#datalayout" ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootSource) "#source" ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootComment) "#comment" ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootMetadata) "#metadata" ppSpace term:1024 "," ppSpace term:1024 "," ppSpace term:1024 : vir_root
scoped syntax:940 (name := viewRootAttrgroup) "#attrgroup" ppSpace term:1024 ppSpace term:1024 : vir_root
scoped syntax:1024 (name := groupVirTleList) "(" vir_tle_list ")" : vir_tle_list
scoped syntax:1024 (name := escapeVirTleList) "{" term "}" : vir_tle_list
scoped syntax:1024 (name := itemsVirTypListOne) vir_typ : vir_typ_list
scoped syntax:900 (name := itemsVirTypListMore) vir_typ "," ppSpace vir_typ_list : vir_typ_list
scoped syntax:1024 (name := itemsVirCodeOne) vir_instr : vir_code
scoped syntax:900 (name := itemsVirCodeMore) vir_instr:920 ";" ppLine vir_code : vir_code
scoped syntax:1024 (name := itemsVirPhisOne) vir_phi : vir_phis
scoped syntax:900 (name := itemsVirPhisMore) vir_phi:920 ";" ppLine vir_phis : vir_phis
scoped syntax:900 (name := itemsVirIdxListMore) vir_idx_list:950 "," ppSpace vir_idx_list : vir_idx_list
scoped syntax:900 (name := itemsVirPhiArgsMore) vir_phi_args:950 "," ppSpace vir_phi_args : vir_phi_args
scoped syntax:900 (name := itemsVirArmListMore) vir_arm_list:950 ";" ppLine vir_arm_list : vir_arm_list
scoped syntax:900 (name := itemsVirLabelListMore) vir_label_list:950 "," ppSpace vir_label_list : vir_label_list
scoped syntax:900 (name := itemsVirAnnsMore) vir_anns:950 ";" ppLine vir_anns : vir_anns
scoped syntax:900 (name := itemsVirFmfMore) vir_fmf:950 "," ppSpace vir_fmf : vir_fmf
scoped syntax:1024 (name := itemsVirDefListOne) term : vir_def_list
scoped syntax:900 (name := itemsVirDefListMore) term:940 ";" ppLine vir_def_list : vir_def_list
scoped syntax:1024 (name := itemsVirDeclListOne) term : vir_decl_list
scoped syntax:900 (name := itemsVirDeclListMore) term:940 ";" ppLine vir_decl_list : vir_decl_list
scoped syntax:1024 (name := itemsVirGlobalListOne) term : vir_global_list
scoped syntax:900 (name := itemsVirGlobalListMore) term:940 ";" ppLine vir_global_list : vir_global_list
scoped syntax:900 (name := itemsVirIidxListMore) vir_iidx_list:950 "," ppSpace vir_iidx_list : vir_iidx_list
scoped syntax:1024 (name := itemsVirBlockListOne) term : vir_block_list
scoped syntax:900 (name := itemsVirBlockListMore) term:940 ";" ppLine ppLine vir_block_list : vir_block_list
scoped syntax:1024 (name := itemsVirTleListOne) term : vir_tle_list
scoped syntax:900 (name := itemsVirTleListMore) term:940 ";" ppLine vir_tle_list : vir_tle_list

meta section

open Lean PrettyPrinter Delaborator SubExpr

private inductive Pattern where
  | wild
  | bindArg
  | ap (head : Lean.Name) (fields : List Pattern)
open Pattern
private abbrev atom (n : Lean.Name) := ap n []

private inductive Piece where
  | token (text : String)
  | arg (n : Nat) (category : Lean.Name)
open Piece
private instance : Coe String Piece := ⟨token⟩

private structure Rule where
  fields : List Pattern
  kind : Lean.Name
  output : List Piece

/-- Constructor fields include implicit parameters, so a partial application never matches. -/
private partial def matchField (s : Lean.SubExpr) (p : Pattern)
    (found : Array Lean.SubExpr) : Option (Array Lean.SubExpr) := do
  match p with
  | .wild => return found
  | .bindArg => return found.push s
  | .ap head fields =>
    guard (s.expr.getAppFn.isConstOf head)
    let args := s.expr.getAppArgs
    guard (args.size == fields.length)
    let mut found := found
    for p in fields, a in args, i in [:args.size] do
      found ← matchField ⟨a, s.pos.pushNaryArg args.size i⟩ p found
    return found

/-- More specific source patterns precede their general cases (e.g. aligned vs. annotated loads). -/
private def forms : Lean.Name → Lean.Name → List Rule
  | `vir_typ, ``dtyp_base.DTYPE_I =>
    [⟨[bindArg], ``viewTypI, ["i", arg 0 `term]⟩]
  | `vir_typ, ``typ.TYPE_I =>
    [⟨[bindArg], ``viewTypI, ["i", arg 0 `term]⟩]
  | `vir_typ, ``dtyp_base.DTYPE_Pointer =>
    [⟨[], ``viewTypPtr, ["ptr"]⟩]
  | `vir_typ, ``typ.TYPE_Pointer => [
    ⟨[(ap ``Option.none [wild])], ``viewTypPtr, ["ptr"]⟩,
    ⟨[(ap ``Option.some [wild, bindArg])], ``viewTypTYPEPointer, [arg 0 `vir_typ, "*"]⟩]
  | `vir_typ, ``dtyp_base.DTYPE_Void =>
    [⟨[], ``viewTypVoid, ["void"]⟩]
  | `vir_typ, ``typ.TYPE_Void =>
    [⟨[], ``viewTypVoid, ["void"]⟩]
  | `vir_typ, ``typ.TYPE_FP => [
    ⟨[(atom ``floating_point_variant.FP_half)], ``viewTypHalf, ["half"]⟩,
    ⟨[(atom ``floating_point_variant.FP_bfloat)], ``viewTypBfloat, ["bfloat"]⟩,
    ⟨[(atom ``floating_point_variant.FP_float)], ``viewTypFloat, ["float"]⟩,
    ⟨[(atom ``floating_point_variant.FP_double)], ``viewTypDouble, ["double"]⟩,
    ⟨[(atom ``floating_point_variant.FP_fp128)], ``viewTypFp128, ["fp128"]⟩,
    ⟨[(atom ``floating_point_variant.FP_x86_fp80)], ``viewTypX86Fp80, ["x86_fp80"]⟩,
    ⟨[(atom ``floating_point_variant.FP_ppc_fp128)], ``viewTypPpcFp128, ["ppc_fp128"]⟩]
  | `vir_typ, ``dtyp_base.DTYPE_FP => [
    ⟨[(atom ``floating_point_variant.FP_half)], ``viewTypHalf, ["half"]⟩,
    ⟨[(atom ``floating_point_variant.FP_bfloat)], ``viewTypBfloat, ["bfloat"]⟩,
    ⟨[(atom ``floating_point_variant.FP_float)], ``viewTypFloat, ["float"]⟩,
    ⟨[(atom ``floating_point_variant.FP_double)], ``viewTypDouble, ["double"]⟩,
    ⟨[(atom ``floating_point_variant.FP_fp128)], ``viewTypFp128, ["fp128"]⟩,
    ⟨[(atom ``floating_point_variant.FP_x86_fp80)], ``viewTypX86Fp80, ["x86_fp80"]⟩,
    ⟨[(atom ``floating_point_variant.FP_ppc_fp128)], ``viewTypPpcFp128, ["ppc_fp128"]⟩]
  | `vir_typ, ``typ.TYPE_Iptr =>
    [⟨[], ``viewTypIptr, ["iptr"]⟩]
  | `vir_typ, ``typ.TYPE_Label =>
    [⟨[], ``viewTypLabel, ["label"]⟩]
  | `vir_typ, ``dtyp_base.DTYPE_Label =>
    [⟨[], ``viewTypLabel, ["label"]⟩]
  | `vir_typ, ``typ.TYPE_Token =>
    [⟨[], ``viewTypToken, ["token"]⟩]
  | `vir_typ, ``typ.TYPE_Metadata =>
    [⟨[], ``viewTypMetadata, ["metadata"]⟩]
  | `vir_typ, ``typ.TYPE_Opaque =>
    [⟨[], ``viewTypOpaque, ["opaque"]⟩]
  | `vir_typ, ``typ.TYPE_Array =>
    [⟨[bindArg, bindArg], ``viewTypX, ["[", arg 0 `term, "x", arg 1 `vir_typ, "]"]⟩]
  | `vir_typ, ``dtyp.DTYPE_Array => [
    ⟨[(atom ``Bool.false), bindArg, bindArg], ``viewTypX, ["[", arg 0 `term, "x", arg 1 `vir_typ, "]"]⟩,
    ⟨[(atom ``Bool.true), bindArg, bindArg], ``viewTypX2, ["<", arg 0 `term, "x", arg 1 `vir_typ, ">"]⟩]
  | `vir_typ, ``typ.TYPE_Vector =>
    [⟨[bindArg, bindArg], ``viewTypX2, ["<", arg 0 `term, "x", arg 1 `vir_typ, ">"]⟩]
  | `vir_typ, ``typ.TYPE_Struct => [
    ⟨[(ap ``List.nil [wild])], ``viewTyp, ["{|", "|}"]⟩,
    ⟨[bindArg], ``viewTyp2, ["{|", arg 0 `vir_typ_list, "|}"]⟩]
  | `vir_typ, ``dtyp.DTYPE_Struct => [
    ⟨[(atom ``Bool.false), (ap ``List.nil [wild])], ``viewTyp, ["{|", "|}"]⟩,
    ⟨[(atom ``Bool.false), bindArg], ``viewTyp2, ["{|", arg 0 `vir_typ_list, "|}"]⟩,
    ⟨[(atom ``Bool.true), (ap ``List.nil [wild])], ``viewTyp3, ["<{", "}>"]⟩,
    ⟨[(atom ``Bool.true), bindArg], ``viewTyp4, ["<{", arg 0 `vir_typ_list, "}>"]⟩]
  | `vir_typ, ``typ.TYPE_Packed_struct => [
    ⟨[(ap ``List.nil [wild])], ``viewTyp3, ["<{", "}>"]⟩,
    ⟨[bindArg], ``viewTyp4, ["<{", arg 0 `vir_typ_list, "}>"]⟩]
  | `vir_typ, ``typ.TYPE_Function => [
    ⟨[bindArg, (ap ``List.nil [wild]), (atom ``Bool.false)], ``viewTyp5, [arg 0 `vir_typ, "(", ")"]⟩,
    ⟨[bindArg, bindArg, (atom ``Bool.false)], ``viewTyp6, [arg 0 `vir_typ, "(", arg 1 `vir_typ_list, ")"]⟩,
    ⟨[bindArg, (ap ``List.nil [wild]), (atom ``Bool.true)], ``viewTyp7, [arg 0 `vir_typ, "(", "...", ")"]⟩,
    ⟨[bindArg, bindArg, (atom ``Bool.true)], ``viewTyp8, [arg 0 `vir_typ, "(", arg 1 `vir_typ_list, ",", "...", ")"]⟩]
  | `vir_typ, ``typ.TYPE_Identified => [
    ⟨[(ap ``«ident».ID_Local [bindArg])], ``viewTypTYPEIdentified, ["%", arg 0 `term]⟩,
    ⟨[(ap ``«ident».ID_Global [bindArg])], ``viewTypTYPEIdentified2, ["@", arg 0 `term]⟩]
  | `vir_exp, ``exp.EXP_Ident => [
    ⟨[wild, (ap ``«ident».ID_Local [bindArg])], ``viewExpEXPIdent, ["%", arg 0 `term]⟩,
    ⟨[wild, (ap ``«ident».ID_Global [bindArg])], ``viewExpEXPIdent2, ["@", arg 0 `term]⟩]
  | `vir_exp, ``exp.EXP_Integer => [
    ⟨[wild, (ap ``Number.signed_int.ofInt [bindArg])], ``viewExpEXPInteger, [arg 0 `term]⟩,
    ⟨[wild, bindArg], ``viewExpEXPInteger, [arg 0 `term]⟩]
  | `vir_exp, ``exp.EXP_Null =>
    [⟨[wild], ``viewExpNull, ["null"]⟩]
  | `vir_exp, ``exp.EXP_Zero_initializer =>
    [⟨[wild], ``viewExpZeroinitializer, ["zeroinitializer"]⟩]
  | `vir_exp, ``exp.EXP_Undef =>
    [⟨[wild], ``viewExpUndef, ["undef"]⟩]
  | `vir_exp, ``exp.EXP_Poison =>
    [⟨[wild], ``viewExpPoison, ["poison"]⟩]
  | `vir_exp, ``exp.EXP_Float =>
    [⟨[wild, bindArg], ``viewExpFp, ["fp", arg 0 `term]⟩]
  | `vir_exp, ``exp.EXP_Metadata =>
    [⟨[wild, bindArg], ``viewExpMeta, ["meta", arg 0 `term]⟩]
  | `vir_exp, ``exp.EXP_Splat =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpSplat, ["splat", arg 0 `vir_typ, arg 1 `vir_exp]⟩]
  | `vir_exp, ``exp.EXP_BlockAddress =>
    [⟨[wild, bindArg, bindArg], ``viewExpBlockaddress, ["blockaddress", "(", arg 0 `term, ",", arg 1 `term, ")"]⟩]
  | `vir_exp, ``exp.EXP_Bool => [
    ⟨[wild, (atom ``Bool.true)], ``viewExpTrue, ["true"]⟩,
    ⟨[wild, (atom ``Bool.false)], ``viewExpFalse, ["false"]⟩]
  | `vir_exp, ``exp.EXP_Cstring =>
    [⟨[wild, bindArg], ``viewExpC, ["c", "[", arg 0 `vir_idx_list, "]"]⟩]
  | `vir_exp, ``exp.EXP_Struct =>
    [⟨[wild, bindArg], ``viewExp, ["{|", arg 0 `vir_idx_list, "|}"]⟩]
  | `vir_exp, ``exp.EXP_Packed_struct =>
    [⟨[wild, bindArg], ``viewExp2, ["<{", arg 0 `vir_idx_list, "}>"]⟩]
  | `vir_exp, ``exp.EXP_Array =>
    [⟨[wild, bindArg], ``viewExp3, ["[", arg 0 `vir_idx_list, "]"]⟩]
  | `vir_exp, ``exp.EXP_Vector =>
    [⟨[wild, bindArg], ``viewExp4, ["<", arg 0 `vir_idx_list, ">"]⟩]
  | `vir_exp, ``exp.OP_IBinop => [
    ⟨[wild, (ap ``ibinop.Add [(atom ``Bool.false), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpAdd, ["add", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Add [(atom ``Bool.true), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpAddNuw, ["add", "nuw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Add [(atom ``Bool.false), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpAddNsw, ["add", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Add [(atom ``Bool.true), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpAddNuwNsw, ["add", "nuw", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Sub [(atom ``Bool.false), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpSub, ["sub", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Sub [(atom ``Bool.true), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpSubNuw, ["sub", "nuw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Sub [(atom ``Bool.false), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpSubNsw, ["sub", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Sub [(atom ``Bool.true), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpSubNuwNsw, ["sub", "nuw", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Mul [(atom ``Bool.false), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpMul, ["mul", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Mul [(atom ``Bool.true), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpMulNuw, ["mul", "nuw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Mul [(atom ``Bool.false), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpMulNsw, ["mul", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Mul [(atom ``Bool.true), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpMulNuwNsw, ["mul", "nuw", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Shl [(atom ``Bool.false), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpShl, ["shl", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Shl [(atom ``Bool.true), (atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpShlNuw, ["shl", "nuw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Shl [(atom ``Bool.false), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpShlNsw, ["shl", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Shl [(atom ``Bool.true), (atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpShlNuwNsw, ["shl", "nuw", "nsw", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.UDiv [(atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpUdiv, ["udiv", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.UDiv [(atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpUdivExact, ["udiv", "exact", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.SDiv [(atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpSdiv, ["sdiv", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.SDiv [(atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpSdivExact, ["sdiv", "exact", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.LShr [(atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpLshr, ["lshr", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.LShr [(atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpLshrExact, ["lshr", "exact", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.AShr [(atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpAshr, ["ashr", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.AShr [(atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpAshrExact, ["ashr", "exact", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``ibinop.URem), wild, bindArg, bindArg], ``viewExpUrem, ["urem", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``ibinop.SRem), wild, bindArg, bindArg], ``viewExpSrem, ["srem", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``ibinop.And), wild, bindArg, bindArg], ``viewExpAnd, ["and", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Or [(atom ``Bool.false)]), wild, bindArg, bindArg], ``viewExpOr, ["or", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (ap ``ibinop.Or [(atom ``Bool.true)]), wild, bindArg, bindArg], ``viewExpOrDisjoint, ["or", "disjoint", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``ibinop.Xor), wild, bindArg, bindArg], ``viewExpXor, ["xor", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_ICmp => [
    ⟨[wild, wild, (atom ``icmp.Eq), wild, bindArg, bindArg], ``viewExpIcmpEq, ["icmp", "eq", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Ne), wild, bindArg, bindArg], ``viewExpIcmpNe, ["icmp", "ne", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Ugt), wild, bindArg, bindArg], ``viewExpIcmpUgt, ["icmp", "ugt", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Uge), wild, bindArg, bindArg], ``viewExpIcmpUge, ["icmp", "uge", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Ult), wild, bindArg, bindArg], ``viewExpIcmpUlt, ["icmp", "ult", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Ule), wild, bindArg, bindArg], ``viewExpIcmpUle, ["icmp", "ule", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Sgt), wild, bindArg, bindArg], ``viewExpIcmpSgt, ["icmp", "sgt", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Sge), wild, bindArg, bindArg], ``viewExpIcmpSge, ["icmp", "sge", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Slt), wild, bindArg, bindArg], ``viewExpIcmpSlt, ["icmp", "slt", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (atom ``icmp.Sle), wild, bindArg, bindArg], ``viewExpIcmpSle, ["icmp", "sle", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_FBinop => [
    ⟨[wild, (atom ``fbinop.FAdd), wild, wild, bindArg, bindArg], ``viewExpFadd, ["fadd", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fbinop.FSub), wild, wild, bindArg, bindArg], ``viewExpFsub, ["fsub", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fbinop.FMul), wild, wild, bindArg, bindArg], ``viewExpFmul, ["fmul", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fbinop.FDiv), wild, wild, bindArg, bindArg], ``viewExpFdiv, ["fdiv", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fbinop.FRem), wild, wild, bindArg, bindArg], ``viewExpFrem, ["frem", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_FCmp => [
    ⟨[wild, (atom ``fcmp.FFalse), wild, wild, wild, wild], ``viewExpFcmpFalse, ["fcmp", "false"]⟩,
    ⟨[wild, (atom ``fcmp.FTrue), wild, wild, wild, wild], ``viewExpFcmpTrue, ["fcmp", "true"]⟩,
    ⟨[wild, (atom ``fcmp.FOeq), wild, wild, bindArg, bindArg], ``viewExpFcmpOeq, ["fcmp", "oeq", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FOgt), wild, wild, bindArg, bindArg], ``viewExpFcmpOgt, ["fcmp", "ogt", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FOge), wild, wild, bindArg, bindArg], ``viewExpFcmpOge, ["fcmp", "oge", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FOlt), wild, wild, bindArg, bindArg], ``viewExpFcmpOlt, ["fcmp", "olt", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FOle), wild, wild, bindArg, bindArg], ``viewExpFcmpOle, ["fcmp", "ole", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FOne), wild, wild, bindArg, bindArg], ``viewExpFcmpOne, ["fcmp", "one", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FOrd), wild, wild, bindArg, bindArg], ``viewExpFcmpOrd, ["fcmp", "ord", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FUno), wild, wild, bindArg, bindArg], ``viewExpFcmpUno, ["fcmp", "uno", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FUeq), wild, wild, bindArg, bindArg], ``viewExpFcmpUeq, ["fcmp", "ueq", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FUgt), wild, wild, bindArg, bindArg], ``viewExpFcmpUgt, ["fcmp", "ugt", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FUge), wild, wild, bindArg, bindArg], ``viewExpFcmpUge, ["fcmp", "uge", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FUlt), wild, wild, bindArg, bindArg], ``viewExpFcmpUlt, ["fcmp", "ult", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FUle), wild, wild, bindArg, bindArg], ``viewExpFcmpUle, ["fcmp", "ule", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩,
    ⟨[wild, (atom ``fcmp.FUne), wild, wild, bindArg, bindArg], ``viewExpFcmpUne, ["fcmp", "une", arg 0 `vir_exp, ",", arg 1 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_Conversion => [
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Trunc [(atom ``Bool.false), (atom ``Bool.false)])]), bindArg, bindArg, bindArg], ``viewExpTruncTo, ["trunc", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Trunc [(atom ``Bool.true), (atom ``Bool.false)])]), bindArg, bindArg, bindArg], ``viewExpTruncNuwTo, ["trunc", "nuw", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Trunc [(atom ``Bool.false), (atom ``Bool.true)])]), bindArg, bindArg, bindArg], ``viewExpTruncNswTo, ["trunc", "nsw", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Trunc [(atom ``Bool.true), (atom ``Bool.true)])]), bindArg, bindArg, bindArg], ``viewExpTruncNuwNswTo, ["trunc", "nuw", "nsw", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Zext [(atom ``Bool.false)])]), bindArg, bindArg, bindArg], ``viewExpZextTo, ["zext", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Zext [(atom ``Bool.true)])]), bindArg, bindArg, bindArg], ``viewExpZextNnegTo, ["zext", "nneg", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(atom ``pure_conversion.Sext)]), bindArg, bindArg, bindArg], ``viewExpSextTo, ["sext", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Fptrunc [(ap ``List.nil [wild])])]), bindArg, bindArg, bindArg], ``viewExpFptruncTo, ["fptrunc", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Fptrunc [bindArg])]), bindArg, bindArg, bindArg], ``viewExpFptruncTo2, ["fptrunc", "[", arg 0 `vir_fmf, "]", arg 1 `vir_typ, arg 2 `vir_exp, "to", arg 3 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Fpext [(ap ``List.nil [wild])])]), bindArg, bindArg, bindArg], ``viewExpFpextTo, ["fpext", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Fpext [bindArg])]), bindArg, bindArg, bindArg], ``viewExpFpextTo2, ["fpext", "[", arg 0 `vir_fmf, "]", arg 1 `vir_typ, arg 2 `vir_exp, "to", arg 3 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Uitofp [(atom ``Bool.false)])]), bindArg, bindArg, bindArg], ``viewExpUitofpTo, ["uitofp", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(ap ``pure_conversion.Uitofp [(atom ``Bool.true)])]), bindArg, bindArg, bindArg], ``viewExpUitofpNnegTo, ["uitofp", "nneg", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(atom ``pure_conversion.Sitofp)]), bindArg, bindArg, bindArg], ``viewExpSitofpTo, ["sitofp", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(atom ``pure_conversion.Fptoui)]), bindArg, bindArg, bindArg], ``viewExpFptouiTo, ["fptoui", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Pure [(atom ``pure_conversion.Fptosi)]), bindArg, bindArg, bindArg], ``viewExpFptosiTo, ["fptosi", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Impure [(atom ``impure_conversion.Inttoptr)]), bindArg, bindArg, bindArg], ``viewExpInttoptrTo, ["inttoptr", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Impure [(atom ``impure_conversion.Ptrtoint)]), bindArg, bindArg, bindArg], ``viewExpPtrtointTo, ["ptrtoint", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Impure [(atom ``impure_conversion.Ptrtoaddr)]), bindArg, bindArg, bindArg], ``viewExpPtrtoaddrTo, ["ptrtoaddr", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (atom ``conversion_type.CONV_Bitcast), bindArg, bindArg, bindArg], ``viewExpBitcastTo, ["bitcast", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩,
    ⟨[wild, (ap ``conversion_type.CONV_Impure [(atom ``impure_conversion.Addrspacecast)]), bindArg, bindArg, bindArg], ``viewExpAddrspacecastTo, ["addrspacecast", arg 0 `vir_typ, arg 1 `vir_exp, "to", arg 2 `vir_typ]⟩]
  | `vir_exp, ``exp.OP_Select =>
    [⟨[wild, wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpSelect, ["select", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", arg 4 `vir_typ, arg 5 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_GetElementPtr =>
    [⟨[wild, (atom ``gep_no_flags), bindArg, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg], ``viewExpGetelementptr, ["getelementptr", arg 0 `vir_typ, ",", arg 1 `vir_typ, arg 2 `vir_exp, ",", arg 3 `vir_idx_list]⟩]
  | `vir_exp, ``exp.OP_ExtractElement =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpExtractelement, ["extractelement", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_InsertElement =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpInsertelement, ["insertelement", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", arg 4 `vir_typ, arg 5 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_ShuffleVector =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpShufflevector, ["shufflevector", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", arg 4 `vir_typ, arg 5 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_ExtractValue =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg], ``viewExpExtractvalue, ["extractvalue", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_iidx_list]⟩]
  | `vir_exp, ``exp.OP_InsertValue =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg], ``viewExpInsertvalue, ["insertvalue", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", arg 4 `vir_iidx_list]⟩]
  | `vir_exp, ``exp.OP_Fneg => [
    ⟨[wild, (ap ``List.nil [wild]), (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpFneg, ["fneg", arg 0 `vir_typ, arg 1 `vir_exp]⟩,
    ⟨[wild, bindArg, (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpFneg2, ["fneg", "[", arg 0 `vir_fmf, "]", arg 1 `vir_typ, arg 2 `vir_exp]⟩]
  | `vir_exp, ``exp.OP_Freeze =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewExpFreeze, ["freeze", arg 0 `vir_typ, arg 1 `vir_exp]⟩]
  | `vir_instr, ``Prod.mk => [
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Op [wild, bindArg])]), wild], ``viewInstrProdMk, [arg 0 `term, "=", arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Call [wild, bindArg, bindArg, wild, wild])]), wild], ``viewInstrCall, [arg 0 `term, "=", "call", arg 1 `term, arg 2 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IVoid [wild]), (ap ``instr.INSTR_Call [wild, bindArg, bindArg, wild, wild])]), wild], ``viewInstrCall2, ["call", arg 0 `term, arg 1 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Alloca [wild, bindArg, (ap ``List.nil [wild])])]), wild], ``viewInstrAlloca, [arg 0 `term, "=", "alloca", arg 1 `vir_typ]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Alloca [wild, bindArg, (ap ``List.cons [wild, (ap ``annotation.ANN_align [wild, (ap ``Number.signed_int.ofInt [bindArg])]), (ap ``List.nil [wild])])])]), wild], ``viewInstrAllocaAlign, [arg 0 `term, "=", "alloca", arg 1 `vir_typ, ",", "align", arg 2 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Alloca [wild, bindArg, (ap ``List.cons [wild, (ap ``annotation.ANN_align [wild, bindArg]), (ap ``List.nil [wild])])])]), wild], ``viewInstrAllocaAlign, [arg 0 `term, "=", "alloca", arg 1 `vir_typ, ",", "align", arg 2 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Alloca [wild, bindArg, bindArg])]), wild], ``viewInstrAlloca2, [arg 0 `term, "=", "alloca", arg 1 `vir_typ, ",", arg 2 `vir_anns]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Load [wild, bindArg, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.nil [wild])])]), wild], ``viewInstrLoad, [arg 0 `term, "=", "load", arg 1 `vir_typ, ",", arg 2 `vir_typ, arg 3 `vir_exp]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Load [wild, bindArg, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.cons [wild, (ap ``annotation.ANN_align [wild, (ap ``Number.signed_int.ofInt [bindArg])]), (ap ``List.nil [wild])])])]), wild], ``viewInstrLoadAlign, [arg 0 `term, "=", "load", arg 1 `vir_typ, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", "align", arg 4 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Load [wild, bindArg, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.cons [wild, (ap ``annotation.ANN_align [wild, bindArg]), (ap ``List.nil [wild])])])]), wild], ``viewInstrLoadAlign, [arg 0 `term, "=", "load", arg 1 `vir_typ, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", "align", arg 4 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Load [wild, bindArg, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.cons [wild, (ap ``annotation.ANN_volatile [wild]), (ap ``List.nil [wild])])])]), wild], ``viewInstrLoadVolatile, [arg 0 `term, "=", "load", "volatile", arg 1 `vir_typ, ",", arg 2 `vir_typ, arg 3 `vir_exp]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_Load [wild, bindArg, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg])]), wild], ``viewInstrLoad2, [arg 0 `term, "=", "load", arg 1 `vir_typ, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", arg 4 `vir_anns]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IVoid [wild]), (ap ``instr.INSTR_Store [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.nil [wild])])]), wild], ``viewInstrStore, ["store", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IVoid [wild]), (ap ``instr.INSTR_Store [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.cons [wild, (ap ``annotation.ANN_align [wild, (ap ``Number.signed_int.ofInt [bindArg])]), (ap ``List.nil [wild])])])]), wild], ``viewInstrStoreAlign, ["store", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", "align", arg 4 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IVoid [wild]), (ap ``instr.INSTR_Store [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.cons [wild, (ap ``annotation.ANN_align [wild, bindArg]), (ap ``List.nil [wild])])])]), wild], ``viewInstrStoreAlign, ["store", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", "align", arg 4 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IVoid [wild]), (ap ``instr.INSTR_Store [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``List.cons [wild, (ap ``annotation.ANN_volatile [wild]), (ap ``List.nil [wild])])])]), wild], ``viewInstrStoreVolatile, ["store", "volatile", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IVoid [wild]), (ap ``instr.INSTR_Store [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg])]), wild], ``viewInstrStore2, ["store", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_typ, arg 3 `vir_exp, ",", arg 4 `vir_anns]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``instr.INSTR_Comment [wild, bindArg])]), wild], ``viewInstrComment, ["#comment", arg 0 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``instr.INSTR_Fence [wild, wild, bindArg])]), wild], ``viewInstrFence, ["fence", arg 0 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_AtomicCmpXchg [wild, bindArg])]), wild], ``viewInstrCmpxchg, [arg 0 `term, "=", "cmpxchg", arg 1 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_AtomicRMW [wild, bindArg])]), wild], ``viewInstrAtomicrmw, [arg 0 `term, "=", "atomicrmw", arg 1 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_VAArg [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg])]), wild], ``viewInstrVaArg, [arg 0 `term, "=", "va_arg", arg 1 `vir_typ, arg 2 `vir_exp, ",", arg 3 `vir_typ]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, (ap ``instr_id.IId [bindArg]), (ap ``instr.INSTR_LandingPad [wild, bindArg, wild, wild])]), wild], ``viewInstrLandingpad, [arg 0 `term, "=", "landingpad", arg 1 `vir_typ]⟩]
  | `vir_term, ``Prod.mk => [
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Ret [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg])])]), wild], ``viewTermRet, ["ret", arg 0 `vir_typ, arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Ret_void [wild])]), wild], ``viewTermRetVoid, ["ret", "void"]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Br [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg, bindArg])]), wild], ``viewTermBrLabelLabel, ["br", arg 0 `vir_typ, arg 1 `vir_exp, ",", "label", arg 2 `term, ",", "label", arg 3 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Br_1 [wild, bindArg])]), wild], ``viewTermBrLabel, ["br", "label", arg 0 `term]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Unreachable [wild])]), wild], ``viewTermUnreachable, ["unreachable"]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Resume [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg])])]), wild], ``viewTermResume, ["resume", arg 0 `vir_typ, arg 1 `vir_exp]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Switch [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg, bindArg])]), wild], ``viewTermSwitchLabel, ["switch", arg 0 `vir_typ, arg 1 `vir_exp, ",", "label", arg 2 `term, arg 3 `vir_arm_list]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_IndirectBr [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), bindArg, wild])]), wild], ``viewTermIndirectbr, ["indirectbr", arg 0 `vir_typ, arg 1 `vir_exp, ",", arg 2 `vir_label_list]⟩,
    ⟨[wild, wild, (ap ``Prod.mk [wild, wild, wild, (ap ``terminator.TERM_Invoke [wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg]), wild, bindArg, bindArg, wild, wild])]), wild], ``viewTermInvokeToLabelUnwindLabel, ["invoke", arg 0 `vir_typ, arg 1 `vir_exp, "to", "label", arg 2 `term, "unwind", "label", arg 3 `term]⟩]
  | `vir_phi, ``Prod.mk =>
    [⟨[wild, wild, (ap ``Prod.mk [wild, wild, bindArg, (ap ``phi.Phi [wild, wild, bindArg, bindArg])]), wild], ``viewPhiPhi, [arg 0 `term, "=", "phi", arg 1 `vir_typ, arg 2 `vir_phi_args]⟩]
  | `vir_idx_list, ``Prod.mk =>
    [⟨[wild, wild, bindArg, bindArg], ``viewIdxListProdMk, [arg 0 `vir_typ, arg 1 `vir_exp]⟩]
  | `vir_phi_args, ``Prod.mk =>
    [⟨[wild, wild, bindArg, bindArg], ``viewPhiArgs, ["[", arg 1 `vir_exp, ",", arg 0 `term, "]"]⟩]
  | `vir_arm_list, ``Prod.mk => [
    ⟨[wild, wild, (ap ``tint_literal.TInt_Literal [bindArg, (ap ``Number.signed_int.ofInt [bindArg])]), bindArg], ``viewArmListILabel, [arg 0 `width, arg 1 `term, ",", "label", arg 2 `term]⟩,
    ⟨[wild, wild, (ap ``tint_literal.TInt_Literal [bindArg, bindArg]), bindArg], ``viewArmListILabel, [arg 0 `width, arg 1 `term, ",", "label", arg 2 `term]⟩]
  | `vir_anns, ``annotation.ANN_align => [
    ⟨[wild, (ap ``Number.signed_int.ofInt [bindArg])], ``viewAnnsAlign, ["align", arg 0 `term]⟩,
    ⟨[wild, bindArg], ``viewAnnsAlign, ["align", arg 0 `term]⟩]
  | `vir_anns, ``annotation.ANN_volatile =>
    [⟨[wild], ``viewAnnsVolatile, ["volatile"]⟩]
  | `vir_anns, ``annotation.ANN_atomic =>
    [⟨[wild], ``viewAnnsAtomic, ["atomic"]⟩]
  | `vir_anns, ``annotation.ANN_inalloca =>
    [⟨[wild], ``viewAnnsInalloca, ["inalloca"]⟩]
  | `vir_anns, ``annotation.ANN_num_elements =>
    [⟨[wild, (ap ``Prod.mk [wild, wild, bindArg, bindArg])], ``viewAnnsNumElements, ["num_elements", arg 0 `vir_typ, arg 1 `vir_exp]⟩]
  | `vir_fmf, ``fast_math.Nnan =>
    [⟨[], ``viewFmfNnan, ["nnan"]⟩]
  | `vir_fmf, ``fast_math.Ninf =>
    [⟨[], ``viewFmfNinf, ["ninf"]⟩]
  | `vir_fmf, ``fast_math.Nsz =>
    [⟨[], ``viewFmfNsz, ["nsz"]⟩]
  | `vir_fmf, ``fast_math.Arcp =>
    [⟨[], ``viewFmfArcp, ["arcp"]⟩]
  | `vir_fmf, ``fast_math.Contract =>
    [⟨[], ``viewFmfContract, ["contract"]⟩]
  | `vir_fmf, ``fast_math.Afn =>
    [⟨[], ``viewFmfAfn, ["afn"]⟩]
  | `vir_fmf, ``fast_math.Reassoc =>
    [⟨[], ``viewFmfReassoc, ["reassoc"]⟩]
  | `vir_fmf, ``fast_math.Fast =>
    [⟨[], ``viewFmfFast, ["fast"]⟩]
  | `vir_root, ``definition.mk_definition =>
    [⟨[wild, wild, (ap ``declaration.mk_declaration [wild, (ap ``raw_id.Name [bindArg]), wild, wild, wild, wild]), bindArg, bindArg], ``viewRootFunc, ["func", arg 0 `term, arg 1 `term, ":=", arg 2 `term]⟩]
  | `vir_root, ``block.mk_block => [
    ⟨[wild, bindArg, (ap ``List.nil [wild]), (ap ``List.nil [wild]), bindArg, wild], ``viewRootMkBlock, [arg 0 `term, ":", arg 1 `vir_term]⟩,
    ⟨[wild, bindArg, (ap ``List.nil [wild]), bindArg, bindArg, wild], ``viewRootMkBlock2, [arg 0 `term, ":", arg 1 `vir_code, arg 2 `vir_term]⟩,
    ⟨[wild, bindArg, bindArg, bindArg, bindArg, wild], ``viewRootMkBlock3, [arg 0 `term, ":", arg 1 `vir_phis, arg 2 `vir_code, arg 3 `vir_term]⟩]
  | `vir_iidx_list, ``Number.signed_int.ofInt =>
    [⟨[bindArg], ``viewIidxListZToNumInt, [arg 0 `term]⟩]
  | `vir_root, ``cfg.mkCFG =>
    [⟨[wild, bindArg, bindArg, bindArg], ``viewRootCfg, ["cfg", arg 0 `term, ",", arg 2 `term, "{", arg 1 `vir_block_list, "}"]⟩]
  | `vir_root, ``modul.mk_modul => [
    ⟨[wild, wild, (ap ``Option.none [wild]), (ap ``Option.none [wild]), (ap ``Option.none [wild]), (ap ``List.nil [wild]), (ap ``List.nil [wild]), (ap ``List.nil [wild]), bindArg], ``viewRootModul, ["modul", "{", arg 0 `vir_def_list, "}"]⟩,
    ⟨[wild, wild, (ap ``Option.none [wild]), (ap ``Option.none [wild]), (ap ``Option.none [wild]), (ap ``List.nil [wild]), (ap ``List.nil [wild]), bindArg, bindArg], ``viewRootModul2, ["modul", "{", arg 0 `vir_decl_list, "|", arg 1 `vir_def_list, "}"]⟩]
  | `vir_root, ``«global».mk_global => [
    ⟨[wild, bindArg, bindArg, (atom ``Bool.false), (ap ``Option.some [wild, bindArg]), (atom ``Bool.false), (atom ``Bool.false), (ap ``List.nil [wild])], ``viewRootGlobal, ["global", arg 0 `term, ":", arg 1 `vir_typ, ":=", arg 2 `vir_exp]⟩,
    ⟨[wild, bindArg, bindArg, (atom ``Bool.true), (ap ``Option.some [wild, bindArg]), (atom ``Bool.false), (atom ``Bool.false), (ap ``List.nil [wild])], ``viewRootConstant, ["constant", arg 0 `term, ":", arg 1 `vir_typ, ":=", arg 2 `vir_exp]⟩,
    ⟨[wild, bindArg, bindArg, (atom ``Bool.false), (ap ``Option.none [wild]), (atom ``Bool.true), (atom ``Bool.false), (ap ``List.nil [wild])], ``viewRootExtern, ["extern", arg 0 `term, ":", arg 1 `vir_typ]⟩,
    ⟨[wild, bindArg, bindArg, (atom ``Bool.false), (ap ``Option.some [wild, bindArg]), (atom ``Bool.false), (atom ``Bool.true), (ap ``List.nil [wild])], ``viewRootAlias, ["alias", arg 0 `term, ":", arg 1 `vir_typ, ":=", arg 2 `vir_exp]⟩]
  | `vir_root, ``declaration.mk_declaration =>
    [⟨[wild, bindArg, bindArg, wild, wild, wild], ``viewRootDeclare, ["declare", arg 0 `term, ":", arg 1 `vir_typ]⟩]
  | `vir_root, ``toplevel_entity.TLE_Declaration =>
    [⟨[wild, wild, bindArg], ``viewRootDecl, ["#decl", arg 0 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Definition =>
    [⟨[wild, wild, bindArg], ``viewRootDef, ["#def", arg 0 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Global =>
    [⟨[wild, wild, bindArg], ``viewRootGlobal2, ["#global", arg 0 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Type_decl =>
    [⟨[wild, wild, bindArg, bindArg], ``viewRootType, ["#type", arg 0 `term, ":=", arg 1 `vir_typ]⟩]
  | `vir_root, ``toplevel_entity.TLE_Target =>
    [⟨[wild, wild, bindArg], ``viewRootTarget, ["#target", arg 0 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Datalayout =>
    [⟨[wild, wild, bindArg], ``viewRootDatalayout, ["#datalayout", arg 0 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Source_filename =>
    [⟨[wild, wild, bindArg], ``viewRootSource, ["#source", arg 0 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Comment =>
    [⟨[wild, wild, bindArg], ``viewRootComment, ["#comment", arg 0 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Metadata =>
    [⟨[wild, wild, bindArg, bindArg, bindArg], ``viewRootMetadata, ["#metadata", arg 0 `term, ",", arg 1 `term, ",", arg 2 `term]⟩]
  | `vir_root, ``toplevel_entity.TLE_Attribute_group =>
    [⟨[wild, wild, bindArg, bindArg], ``viewRootAttrgroup, ["#attrgroup", arg 0 `term, arg 1 `term]⟩]
  | _, _ => []

private structure ListForm where
  itemCategory : Lean.Name
  separator : String
  more : Lean.Name
  singleton : Option Lean.Name

private def listForm : Lean.Name → Option ListForm
  | `vir_typ_list => some ⟨`vir_typ, ",", ``itemsVirTypListMore, some ``itemsVirTypListOne⟩
  | `vir_code => some ⟨`vir_instr, ";", ``itemsVirCodeMore, some ``itemsVirCodeOne⟩
  | `vir_phis => some ⟨`vir_phi, ";", ``itemsVirPhisMore, some ``itemsVirPhisOne⟩
  | `vir_idx_list => some ⟨`vir_idx_list, ",", ``itemsVirIdxListMore, none⟩
  | `vir_phi_args => some ⟨`vir_phi_args, ",", ``itemsVirPhiArgsMore, none⟩
  | `vir_arm_list => some ⟨`vir_arm_list, ";", ``itemsVirArmListMore, none⟩
  | `vir_label_list => some ⟨`vir_label_list, ",", ``itemsVirLabelListMore, none⟩
  | `vir_anns => some ⟨`vir_anns, ";", ``itemsVirAnnsMore, none⟩
  | `vir_fmf => some ⟨`vir_fmf, ",", ``itemsVirFmfMore, none⟩
  | `vir_def_list => some ⟨`term, ";", ``itemsVirDefListMore, some ``itemsVirDefListOne⟩
  | `vir_decl_list => some ⟨`term, ";", ``itemsVirDeclListMore, some ``itemsVirDeclListOne⟩
  | `vir_global_list => some ⟨`term, ";", ``itemsVirGlobalListMore, some ``itemsVirGlobalListOne⟩
  | `vir_iidx_list => some ⟨`vir_iidx_list, ",", ``itemsVirIidxListMore, none⟩
  | `vir_block_list => some ⟨`term, ";", ``itemsVirBlockListMore, some ``itemsVirBlockListOne⟩
  | `vir_tle_list => some ⟨`term, ";", ``itemsVirTleListMore, some ``itemsVirTleListOne⟩
  | _ => none

private def escapeKind : Lean.Name → Lean.Name
  | `vir_typ => ``escapeVirTyp
  | `vir_typ_list => ``escapeVirTypList
  | `vir_exp => ``escapeVirExp
  | `vir_instr => ``escapeVirInstr
  | `vir_term => ``escapeVirTerm
  | `vir_code => ``escapeVirCode
  | `vir_phi => ``escapeVirPhi
  | `vir_phis => ``escapeVirPhis
  | `vir_idx_list => ``escapeVirIdxList
  | `vir_phi_args => ``escapeVirPhiArgs
  | `vir_arm_list => ``escapeVirArmList
  | `vir_label_list => ``escapeVirLabelList
  | `vir_anns => ``escapeVirAnns
  | `vir_fmf => ``escapeVirFmf
  | `vir_def_list => ``escapeVirDefList
  | `vir_decl_list => ``escapeVirDeclList
  | `vir_global_list => ``escapeVirGlobalList
  | `vir_iidx_list => ``escapeVirIidxList
  | `vir_block_list => ``escapeVirBlockList
  | `vir_tle_list => ``escapeVirTleList
  | _ => .anonymous

private def node (kind : Lean.Name) (args : Array Syntax) : Syntax := .node .none kind args

/-- Traverse just list constructors; unknown tails use the source's ordinary-term escape. -/
private partial def listItems (s : Lean.SubExpr) (acc : Array Lean.SubExpr := #[]) :
    Option (Array Lean.SubExpr) := do
  if s.expr.isAppOfArity ``List.nil 1 then return acc
  guard (s.expr.isAppOfArity ``List.cons 3)
  let args := s.expr.getAppArgs
  listItems ⟨args[2]!, s.pos.pushNaryArg 3 2⟩ (acc.push ⟨args[1]!, s.pos.pushNaryArg 3 1⟩)

/-- Suppress only the two source coercions, not arbitrary byte-array values. -/
private def ordinary : Delab := do
  let e ← getExpr
  if e.isAppOfArity ``raw_id.Anon 1 then return ← withAppArg delab
  if e.isAppOfArity ``raw_id.Name 1 then
    return ← withAppArg do
      if (← getExpr).isAppOfArity ``String.toUTF8 1 then withAppArg delab else delab
  if e.isAppOfArity ``String.toUTF8 1 then return ← withAppArg delab
  return ← delab

private def literalWidth? (e : Expr) : MetaM (Option Syntax) := do
  unless e.isAppOfArity ``Subtype.mk 4 do return none
  let some n ← Meta.getNatValue? e.appFn!.appArg! | return none
  return some (node ``typeVariable #[(mkIdent (.mkSimple s!"i{n}")).raw])

private partial def render (cat : Lean.Name) (escaped := true) (item := false) : DelabM Syntax := do
  if cat == `term then return (← ordinary).raw
  let s ← readThe Lean.SubExpr
  let e := s.expr
  if cat == `vir_typ && e.isAppOfArity ``dtyp.DTYPE_Base 1 then
    return ← withAppArg (render cat escaped)
  if cat == `width then
    if let some view ← literalWidth? e then return view
    return node ``viewTypI #[mkAtom "i", (← ordinary).raw]
  if cat == `vir_typ && (e.isAppOfArity ``typ.TYPE_I 1 || e.isAppOfArity ``dtyp_base.DTYPE_I 1) then
    if let some view ← literalWidth? e.appArg! then return view
  if !item then
    if let some f := listForm cat then
      if let some items := listItems s then
        if let some x := items.back? then
          let draw := fun (part : Lean.SubExpr) ↦
            withTheReader Lean.SubExpr (fun _ ↦ part) (render f.itemCategory true true)
          let last ← draw x
          let mut result := f.singleton.elim last (fun k ↦ node k #[last])
          for i in [:items.size - 1] do
            let p ← draw items[items.size - 2 - i]!
            result := node f.more #[p, mkAtom f.separator, result]
          return result
      guard escaped
      return node (escapeKind cat) #[mkAtom "{", (← delab).raw, mkAtom "}"]
  if item && cat == `vir_label_list then
    return node ``labelItem #[mkAtom "label", (← ordinary).raw]
  let head := e.getAppFn.constName
  for r in forms cat head do
    if let some found := matchField s (.ap head r.fields) #[] then
      let mut children := #[]
      for piece in r.output do
        match piece with
        | .token text => children := children.push (mkAtom text)
        | .arg n category =>
          let some x := found[n]? | failure
          let child ← withTheReader Lean.SubExpr (fun _ ↦ x) (render category)
          children := children.push child
      return node r.kind children
  if item && cat == `vir_iidx_list then return node ``integerIndex #[(← ordinary).raw]
  guard escaped
  if cat == `vir_typ && e.isFVar then return node ``typeVariable #[(← delab).raw]
  return node (escapeKind cat) #[mkAtom "{", (← delab).raw, mkAtom "}"]

/-- Enter a source custom category explicitly from another delaborator. In particular, list
    categories such as `vir_tle_list` must not claim every ordinary Lean list at the root. -/
def delabEntry (category : Lean.Name) : DelabM Syntax := do
  guard (escapeKind category != .anonymous)
  render category

@[scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp_base.DTYPE_I,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_I,
  scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp_base.DTYPE_Pointer,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Pointer,
  scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp_base.DTYPE_Void,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Void,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_FP,
  scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp_base.DTYPE_FP,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Iptr,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Label,
  scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp_base.DTYPE_Label,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Token,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Metadata,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Opaque,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Array,
  scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp.DTYPE_Array,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Vector,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Struct,
  scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp.DTYPE_Struct,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Packed_struct,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Function,
  scoped delab app.Vellvm.Syntax.LLVMAst.typ.TYPE_Identified,
  scoped delab app.Vellvm.Syntax.DynamicTypes.dtyp.DTYPE_Base]
def delabVirTyp : Delab := whenPPOption getPPNotation do
  return ⟨node ``prefixVirTyp #[mkAtom "%t", ← render `vir_typ false]⟩

@[scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Ident,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Integer,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Null,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Zero_initializer,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Undef,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Poison,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Float,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Metadata,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Splat,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_BlockAddress,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Bool,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Cstring,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Struct,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Packed_struct,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Array,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.EXP_Vector,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_IBinop,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_ICmp,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_FBinop,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_FCmp,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_Conversion,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_Select,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_GetElementPtr,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_ExtractElement,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_InsertElement,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_ShuffleVector,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_ExtractValue,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_InsertValue,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_Fneg,
  scoped delab app.Vellvm.Syntax.LLVMAst.exp.OP_Freeze]
def delabVirExp : Delab := whenPPOption getPPNotation do
  return ⟨node ``prefixVirExp #[mkAtom "%e", ← render `vir_exp false]⟩

@[scoped delab app.Vellvm.Syntax.LLVMAst.definition.mk_definition,
  scoped delab app.Vellvm.Syntax.LLVMAst.block.mk_block,
  scoped delab app.Vellvm.Syntax.CFG.cfg.mkCFG,
  scoped delab app.Vellvm.Syntax.CFG.modul.mk_modul,
  scoped delab app.Vellvm.Syntax.LLVMAst.global.mk_global,
  scoped delab app.Vellvm.Syntax.LLVMAst.declaration.mk_declaration,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Declaration,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Definition,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Global,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Type_decl,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Target,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Datalayout,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Source_filename,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Comment,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Metadata,
  scoped delab app.Vellvm.Syntax.LLVMAst.toplevel_entity.TLE_Attribute_group]
def delabVirRoot : Delab := whenPPOption getPPNotation do
  return ⟨← render `vir_root false⟩

@[scoped delab app.Prod.mk]
def delabTriple : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard (e.isAppOfArity ``Prod.mk 4)
  let lhs := e.appFn!.appArg!
  guard (lhs.isAppOfArity ``Prod.mk 4)
  match lhs.appArg!.getAppFn.constName.getPrefix with
  | ``instr => return ⟨node ``prefixVirInstr #[mkAtom "%i", ← render `vir_instr false]⟩
  | ``terminator => return ⟨node ``prefixVirTerm #[mkAtom "%T", ← render `vir_term false]⟩
  | ``phi => return ⟨node ``prefixVirPhi #[mkAtom "%p", ← render `vir_phi false]⟩
  | _ => failure

end
end Vellvm.Syntax.SurfaceSyntax.VIR_Notations
