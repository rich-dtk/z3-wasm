"use strict";
// THIS FILE IS AUTOMATICALLY GENERATED BY make-ts-wrapper.ts
// DO NOT EDIT IT BY HAND
Object.defineProperty(exports, "__esModule", { value: true });
exports.Z3_goal_prec = exports.Z3_error_code = exports.Z3_ast_print_mode = exports.Z3_param_kind = exports.Z3_decl_kind = exports.Z3_ast_kind = exports.Z3_sort_kind = exports.Z3_parameter_kind = exports.Z3_symbol_kind = exports.Z3_lbool = void 0;
var Z3_lbool;
(function (Z3_lbool) {
    Z3_lbool[Z3_lbool["Z3_L_FALSE"] = -1] = "Z3_L_FALSE";
    Z3_lbool[Z3_lbool["Z3_L_UNDEF"] = 0] = "Z3_L_UNDEF";
    Z3_lbool[Z3_lbool["Z3_L_TRUE"] = 1] = "Z3_L_TRUE";
})(Z3_lbool = exports.Z3_lbool || (exports.Z3_lbool = {}));
var Z3_symbol_kind;
(function (Z3_symbol_kind) {
    Z3_symbol_kind[Z3_symbol_kind["Z3_INT_SYMBOL"] = 0] = "Z3_INT_SYMBOL";
    Z3_symbol_kind[Z3_symbol_kind["Z3_STRING_SYMBOL"] = 1] = "Z3_STRING_SYMBOL";
})(Z3_symbol_kind = exports.Z3_symbol_kind || (exports.Z3_symbol_kind = {}));
var Z3_parameter_kind;
(function (Z3_parameter_kind) {
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_INT"] = 0] = "Z3_PARAMETER_INT";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_DOUBLE"] = 1] = "Z3_PARAMETER_DOUBLE";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_RATIONAL"] = 2] = "Z3_PARAMETER_RATIONAL";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_SYMBOL"] = 3] = "Z3_PARAMETER_SYMBOL";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_SORT"] = 4] = "Z3_PARAMETER_SORT";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_AST"] = 5] = "Z3_PARAMETER_AST";
    Z3_parameter_kind[Z3_parameter_kind["Z3_PARAMETER_FUNC_DECL"] = 6] = "Z3_PARAMETER_FUNC_DECL";
})(Z3_parameter_kind = exports.Z3_parameter_kind || (exports.Z3_parameter_kind = {}));
var Z3_sort_kind;
(function (Z3_sort_kind) {
    Z3_sort_kind[Z3_sort_kind["Z3_UNINTERPRETED_SORT"] = 0] = "Z3_UNINTERPRETED_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_BOOL_SORT"] = 1] = "Z3_BOOL_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_INT_SORT"] = 2] = "Z3_INT_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_REAL_SORT"] = 3] = "Z3_REAL_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_BV_SORT"] = 4] = "Z3_BV_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_ARRAY_SORT"] = 5] = "Z3_ARRAY_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_DATATYPE_SORT"] = 6] = "Z3_DATATYPE_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_RELATION_SORT"] = 7] = "Z3_RELATION_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_FINITE_DOMAIN_SORT"] = 8] = "Z3_FINITE_DOMAIN_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_FLOATING_POINT_SORT"] = 9] = "Z3_FLOATING_POINT_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_ROUNDING_MODE_SORT"] = 10] = "Z3_ROUNDING_MODE_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_SEQ_SORT"] = 11] = "Z3_SEQ_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_RE_SORT"] = 12] = "Z3_RE_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_CHAR_SORT"] = 13] = "Z3_CHAR_SORT";
    Z3_sort_kind[Z3_sort_kind["Z3_UNKNOWN_SORT"] = 1000] = "Z3_UNKNOWN_SORT";
})(Z3_sort_kind = exports.Z3_sort_kind || (exports.Z3_sort_kind = {}));
var Z3_ast_kind;
(function (Z3_ast_kind) {
    Z3_ast_kind[Z3_ast_kind["Z3_NUMERAL_AST"] = 0] = "Z3_NUMERAL_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_APP_AST"] = 1] = "Z3_APP_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_VAR_AST"] = 2] = "Z3_VAR_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_QUANTIFIER_AST"] = 3] = "Z3_QUANTIFIER_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_SORT_AST"] = 4] = "Z3_SORT_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_FUNC_DECL_AST"] = 5] = "Z3_FUNC_DECL_AST";
    Z3_ast_kind[Z3_ast_kind["Z3_UNKNOWN_AST"] = 1000] = "Z3_UNKNOWN_AST";
})(Z3_ast_kind = exports.Z3_ast_kind || (exports.Z3_ast_kind = {}));
var Z3_decl_kind;
(function (Z3_decl_kind) {
    Z3_decl_kind[Z3_decl_kind["Z3_OP_TRUE"] = 256] = "Z3_OP_TRUE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FALSE"] = 257] = "Z3_OP_FALSE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EQ"] = 258] = "Z3_OP_EQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DISTINCT"] = 259] = "Z3_OP_DISTINCT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ITE"] = 260] = "Z3_OP_ITE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_AND"] = 261] = "Z3_OP_AND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_OR"] = 262] = "Z3_OP_OR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IFF"] = 263] = "Z3_OP_IFF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_XOR"] = 264] = "Z3_OP_XOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_NOT"] = 265] = "Z3_OP_NOT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IMPLIES"] = 266] = "Z3_OP_IMPLIES";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_OEQ"] = 267] = "Z3_OP_OEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ANUM"] = 512] = "Z3_OP_ANUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_AGNUM"] = 513] = "Z3_OP_AGNUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LE"] = 514] = "Z3_OP_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_GE"] = 515] = "Z3_OP_GE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LT"] = 516] = "Z3_OP_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_GT"] = 517] = "Z3_OP_GT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ADD"] = 518] = "Z3_OP_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SUB"] = 519] = "Z3_OP_SUB";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UMINUS"] = 520] = "Z3_OP_UMINUS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_MUL"] = 521] = "Z3_OP_MUL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DIV"] = 522] = "Z3_OP_DIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IDIV"] = 523] = "Z3_OP_IDIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_REM"] = 524] = "Z3_OP_REM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_MOD"] = 525] = "Z3_OP_MOD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_TO_REAL"] = 526] = "Z3_OP_TO_REAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_TO_INT"] = 527] = "Z3_OP_TO_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_IS_INT"] = 528] = "Z3_OP_IS_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_POWER"] = 529] = "Z3_OP_POWER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STORE"] = 768] = "Z3_OP_STORE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SELECT"] = 769] = "Z3_OP_SELECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CONST_ARRAY"] = 770] = "Z3_OP_CONST_ARRAY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ARRAY_MAP"] = 771] = "Z3_OP_ARRAY_MAP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ARRAY_DEFAULT"] = 772] = "Z3_OP_ARRAY_DEFAULT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_UNION"] = 773] = "Z3_OP_SET_UNION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_INTERSECT"] = 774] = "Z3_OP_SET_INTERSECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_DIFFERENCE"] = 775] = "Z3_OP_SET_DIFFERENCE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_COMPLEMENT"] = 776] = "Z3_OP_SET_COMPLEMENT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_SUBSET"] = 777] = "Z3_OP_SET_SUBSET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_AS_ARRAY"] = 778] = "Z3_OP_AS_ARRAY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ARRAY_EXT"] = 779] = "Z3_OP_ARRAY_EXT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_HAS_SIZE"] = 780] = "Z3_OP_SET_HAS_SIZE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SET_CARD"] = 781] = "Z3_OP_SET_CARD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNUM"] = 1024] = "Z3_OP_BNUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BIT1"] = 1025] = "Z3_OP_BIT1";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BIT0"] = 1026] = "Z3_OP_BIT0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNEG"] = 1027] = "Z3_OP_BNEG";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BADD"] = 1028] = "Z3_OP_BADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSUB"] = 1029] = "Z3_OP_BSUB";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BMUL"] = 1030] = "Z3_OP_BMUL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSDIV"] = 1031] = "Z3_OP_BSDIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUDIV"] = 1032] = "Z3_OP_BUDIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSREM"] = 1033] = "Z3_OP_BSREM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUREM"] = 1034] = "Z3_OP_BUREM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMOD"] = 1035] = "Z3_OP_BSMOD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSDIV0"] = 1036] = "Z3_OP_BSDIV0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUDIV0"] = 1037] = "Z3_OP_BUDIV0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSREM0"] = 1038] = "Z3_OP_BSREM0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUREM0"] = 1039] = "Z3_OP_BUREM0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMOD0"] = 1040] = "Z3_OP_BSMOD0";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ULEQ"] = 1041] = "Z3_OP_ULEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SLEQ"] = 1042] = "Z3_OP_SLEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UGEQ"] = 1043] = "Z3_OP_UGEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SGEQ"] = 1044] = "Z3_OP_SGEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ULT"] = 1045] = "Z3_OP_ULT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SLT"] = 1046] = "Z3_OP_SLT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UGT"] = 1047] = "Z3_OP_UGT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SGT"] = 1048] = "Z3_OP_SGT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BAND"] = 1049] = "Z3_OP_BAND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BOR"] = 1050] = "Z3_OP_BOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNOT"] = 1051] = "Z3_OP_BNOT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BXOR"] = 1052] = "Z3_OP_BXOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNAND"] = 1053] = "Z3_OP_BNAND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BNOR"] = 1054] = "Z3_OP_BNOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BXNOR"] = 1055] = "Z3_OP_BXNOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CONCAT"] = 1056] = "Z3_OP_CONCAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SIGN_EXT"] = 1057] = "Z3_OP_SIGN_EXT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ZERO_EXT"] = 1058] = "Z3_OP_ZERO_EXT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EXTRACT"] = 1059] = "Z3_OP_EXTRACT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_REPEAT"] = 1060] = "Z3_OP_REPEAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BREDOR"] = 1061] = "Z3_OP_BREDOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BREDAND"] = 1062] = "Z3_OP_BREDAND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BCOMP"] = 1063] = "Z3_OP_BCOMP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSHL"] = 1064] = "Z3_OP_BSHL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BLSHR"] = 1065] = "Z3_OP_BLSHR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BASHR"] = 1066] = "Z3_OP_BASHR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ROTATE_LEFT"] = 1067] = "Z3_OP_ROTATE_LEFT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_ROTATE_RIGHT"] = 1068] = "Z3_OP_ROTATE_RIGHT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EXT_ROTATE_LEFT"] = 1069] = "Z3_OP_EXT_ROTATE_LEFT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_EXT_ROTATE_RIGHT"] = 1070] = "Z3_OP_EXT_ROTATE_RIGHT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BIT2BOOL"] = 1071] = "Z3_OP_BIT2BOOL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_INT2BV"] = 1072] = "Z3_OP_INT2BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BV2INT"] = 1073] = "Z3_OP_BV2INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CARRY"] = 1074] = "Z3_OP_CARRY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_XOR3"] = 1075] = "Z3_OP_XOR3";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMUL_NO_OVFL"] = 1076] = "Z3_OP_BSMUL_NO_OVFL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUMUL_NO_OVFL"] = 1077] = "Z3_OP_BUMUL_NO_OVFL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMUL_NO_UDFL"] = 1078] = "Z3_OP_BSMUL_NO_UDFL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSDIV_I"] = 1079] = "Z3_OP_BSDIV_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUDIV_I"] = 1080] = "Z3_OP_BUDIV_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSREM_I"] = 1081] = "Z3_OP_BSREM_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BUREM_I"] = 1082] = "Z3_OP_BUREM_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_BSMOD_I"] = 1083] = "Z3_OP_BSMOD_I";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_UNDEF"] = 1280] = "Z3_OP_PR_UNDEF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TRUE"] = 1281] = "Z3_OP_PR_TRUE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_ASSERTED"] = 1282] = "Z3_OP_PR_ASSERTED";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_GOAL"] = 1283] = "Z3_OP_PR_GOAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_MODUS_PONENS"] = 1284] = "Z3_OP_PR_MODUS_PONENS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REFLEXIVITY"] = 1285] = "Z3_OP_PR_REFLEXIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_SYMMETRY"] = 1286] = "Z3_OP_PR_SYMMETRY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TRANSITIVITY"] = 1287] = "Z3_OP_PR_TRANSITIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TRANSITIVITY_STAR"] = 1288] = "Z3_OP_PR_TRANSITIVITY_STAR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_MONOTONICITY"] = 1289] = "Z3_OP_PR_MONOTONICITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_QUANT_INTRO"] = 1290] = "Z3_OP_PR_QUANT_INTRO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_BIND"] = 1291] = "Z3_OP_PR_BIND";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DISTRIBUTIVITY"] = 1292] = "Z3_OP_PR_DISTRIBUTIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_AND_ELIM"] = 1293] = "Z3_OP_PR_AND_ELIM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_NOT_OR_ELIM"] = 1294] = "Z3_OP_PR_NOT_OR_ELIM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REWRITE"] = 1295] = "Z3_OP_PR_REWRITE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REWRITE_STAR"] = 1296] = "Z3_OP_PR_REWRITE_STAR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_PULL_QUANT"] = 1297] = "Z3_OP_PR_PULL_QUANT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_PUSH_QUANT"] = 1298] = "Z3_OP_PR_PUSH_QUANT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_ELIM_UNUSED_VARS"] = 1299] = "Z3_OP_PR_ELIM_UNUSED_VARS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DER"] = 1300] = "Z3_OP_PR_DER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_QUANT_INST"] = 1301] = "Z3_OP_PR_QUANT_INST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_HYPOTHESIS"] = 1302] = "Z3_OP_PR_HYPOTHESIS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_LEMMA"] = 1303] = "Z3_OP_PR_LEMMA";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_UNIT_RESOLUTION"] = 1304] = "Z3_OP_PR_UNIT_RESOLUTION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_IFF_TRUE"] = 1305] = "Z3_OP_PR_IFF_TRUE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_IFF_FALSE"] = 1306] = "Z3_OP_PR_IFF_FALSE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_COMMUTATIVITY"] = 1307] = "Z3_OP_PR_COMMUTATIVITY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DEF_AXIOM"] = 1308] = "Z3_OP_PR_DEF_AXIOM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_ASSUMPTION_ADD"] = 1309] = "Z3_OP_PR_ASSUMPTION_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_LEMMA_ADD"] = 1310] = "Z3_OP_PR_LEMMA_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_REDUNDANT_DEL"] = 1311] = "Z3_OP_PR_REDUNDANT_DEL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_CLAUSE_TRAIL"] = 1312] = "Z3_OP_PR_CLAUSE_TRAIL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_DEF_INTRO"] = 1313] = "Z3_OP_PR_DEF_INTRO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_APPLY_DEF"] = 1314] = "Z3_OP_PR_APPLY_DEF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_IFF_OEQ"] = 1315] = "Z3_OP_PR_IFF_OEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_NNF_POS"] = 1316] = "Z3_OP_PR_NNF_POS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_NNF_NEG"] = 1317] = "Z3_OP_PR_NNF_NEG";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_SKOLEMIZE"] = 1318] = "Z3_OP_PR_SKOLEMIZE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_MODUS_PONENS_OEQ"] = 1319] = "Z3_OP_PR_MODUS_PONENS_OEQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_TH_LEMMA"] = 1320] = "Z3_OP_PR_TH_LEMMA";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PR_HYPER_RESOLVE"] = 1321] = "Z3_OP_PR_HYPER_RESOLVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_STORE"] = 1536] = "Z3_OP_RA_STORE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_EMPTY"] = 1537] = "Z3_OP_RA_EMPTY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_IS_EMPTY"] = 1538] = "Z3_OP_RA_IS_EMPTY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_JOIN"] = 1539] = "Z3_OP_RA_JOIN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_UNION"] = 1540] = "Z3_OP_RA_UNION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_WIDEN"] = 1541] = "Z3_OP_RA_WIDEN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_PROJECT"] = 1542] = "Z3_OP_RA_PROJECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_FILTER"] = 1543] = "Z3_OP_RA_FILTER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_NEGATION_FILTER"] = 1544] = "Z3_OP_RA_NEGATION_FILTER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_RENAME"] = 1545] = "Z3_OP_RA_RENAME";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_COMPLEMENT"] = 1546] = "Z3_OP_RA_COMPLEMENT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_SELECT"] = 1547] = "Z3_OP_RA_SELECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RA_CLONE"] = 1548] = "Z3_OP_RA_CLONE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FD_CONSTANT"] = 1549] = "Z3_OP_FD_CONSTANT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FD_LT"] = 1550] = "Z3_OP_FD_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_UNIT"] = 1551] = "Z3_OP_SEQ_UNIT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_EMPTY"] = 1552] = "Z3_OP_SEQ_EMPTY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_CONCAT"] = 1553] = "Z3_OP_SEQ_CONCAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_PREFIX"] = 1554] = "Z3_OP_SEQ_PREFIX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_SUFFIX"] = 1555] = "Z3_OP_SEQ_SUFFIX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_CONTAINS"] = 1556] = "Z3_OP_SEQ_CONTAINS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_EXTRACT"] = 1557] = "Z3_OP_SEQ_EXTRACT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE"] = 1558] = "Z3_OP_SEQ_REPLACE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE_RE"] = 1559] = "Z3_OP_SEQ_REPLACE_RE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE_RE_ALL"] = 1560] = "Z3_OP_SEQ_REPLACE_RE_ALL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_REPLACE_ALL"] = 1561] = "Z3_OP_SEQ_REPLACE_ALL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_AT"] = 1562] = "Z3_OP_SEQ_AT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_NTH"] = 1563] = "Z3_OP_SEQ_NTH";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_LENGTH"] = 1564] = "Z3_OP_SEQ_LENGTH";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_INDEX"] = 1565] = "Z3_OP_SEQ_INDEX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_LAST_INDEX"] = 1566] = "Z3_OP_SEQ_LAST_INDEX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_TO_RE"] = 1567] = "Z3_OP_SEQ_TO_RE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SEQ_IN_RE"] = 1568] = "Z3_OP_SEQ_IN_RE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STR_TO_INT"] = 1569] = "Z3_OP_STR_TO_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_INT_TO_STR"] = 1570] = "Z3_OP_INT_TO_STR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UBV_TO_STR"] = 1571] = "Z3_OP_UBV_TO_STR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SBV_TO_STR"] = 1572] = "Z3_OP_SBV_TO_STR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STR_TO_CODE"] = 1573] = "Z3_OP_STR_TO_CODE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STR_FROM_CODE"] = 1574] = "Z3_OP_STR_FROM_CODE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STRING_LT"] = 1575] = "Z3_OP_STRING_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_STRING_LE"] = 1576] = "Z3_OP_STRING_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_PLUS"] = 1577] = "Z3_OP_RE_PLUS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_STAR"] = 1578] = "Z3_OP_RE_STAR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_OPTION"] = 1579] = "Z3_OP_RE_OPTION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_CONCAT"] = 1580] = "Z3_OP_RE_CONCAT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_UNION"] = 1581] = "Z3_OP_RE_UNION";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_RANGE"] = 1582] = "Z3_OP_RE_RANGE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_DIFF"] = 1583] = "Z3_OP_RE_DIFF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_INTERSECT"] = 1584] = "Z3_OP_RE_INTERSECT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_LOOP"] = 1585] = "Z3_OP_RE_LOOP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_POWER"] = 1586] = "Z3_OP_RE_POWER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_COMPLEMENT"] = 1587] = "Z3_OP_RE_COMPLEMENT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_EMPTY_SET"] = 1588] = "Z3_OP_RE_EMPTY_SET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_FULL_SET"] = 1589] = "Z3_OP_RE_FULL_SET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_FULL_CHAR_SET"] = 1590] = "Z3_OP_RE_FULL_CHAR_SET";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_OF_PRED"] = 1591] = "Z3_OP_RE_OF_PRED";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_REVERSE"] = 1592] = "Z3_OP_RE_REVERSE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RE_DERIVATIVE"] = 1593] = "Z3_OP_RE_DERIVATIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_CONST"] = 1594] = "Z3_OP_CHAR_CONST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_LE"] = 1595] = "Z3_OP_CHAR_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_TO_INT"] = 1596] = "Z3_OP_CHAR_TO_INT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_TO_BV"] = 1597] = "Z3_OP_CHAR_TO_BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_FROM_BV"] = 1598] = "Z3_OP_CHAR_FROM_BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_CHAR_IS_DIGIT"] = 1599] = "Z3_OP_CHAR_IS_DIGIT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LABEL"] = 1792] = "Z3_OP_LABEL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_LABEL_LIT"] = 1793] = "Z3_OP_LABEL_LIT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_CONSTRUCTOR"] = 2048] = "Z3_OP_DT_CONSTRUCTOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_RECOGNISER"] = 2049] = "Z3_OP_DT_RECOGNISER";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_IS"] = 2050] = "Z3_OP_DT_IS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_ACCESSOR"] = 2051] = "Z3_OP_DT_ACCESSOR";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_DT_UPDATE_FIELD"] = 2052] = "Z3_OP_DT_UPDATE_FIELD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_AT_MOST"] = 2304] = "Z3_OP_PB_AT_MOST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_AT_LEAST"] = 2305] = "Z3_OP_PB_AT_LEAST";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_LE"] = 2306] = "Z3_OP_PB_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_GE"] = 2307] = "Z3_OP_PB_GE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_PB_EQ"] = 2308] = "Z3_OP_PB_EQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_LO"] = 40960] = "Z3_OP_SPECIAL_RELATION_LO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_PO"] = 40961] = "Z3_OP_SPECIAL_RELATION_PO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_PLO"] = 40962] = "Z3_OP_SPECIAL_RELATION_PLO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_TO"] = 40963] = "Z3_OP_SPECIAL_RELATION_TO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_TC"] = 40964] = "Z3_OP_SPECIAL_RELATION_TC";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_SPECIAL_RELATION_TRC"] = 40965] = "Z3_OP_SPECIAL_RELATION_TRC";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN"] = 45056] = "Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY"] = 45057] = "Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_TOWARD_POSITIVE"] = 45058] = "Z3_OP_FPA_RM_TOWARD_POSITIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_TOWARD_NEGATIVE"] = 45059] = "Z3_OP_FPA_RM_TOWARD_NEGATIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_RM_TOWARD_ZERO"] = 45060] = "Z3_OP_FPA_RM_TOWARD_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_NUM"] = 45061] = "Z3_OP_FPA_NUM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_PLUS_INF"] = 45062] = "Z3_OP_FPA_PLUS_INF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MINUS_INF"] = 45063] = "Z3_OP_FPA_MINUS_INF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_NAN"] = 45064] = "Z3_OP_FPA_NAN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_PLUS_ZERO"] = 45065] = "Z3_OP_FPA_PLUS_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MINUS_ZERO"] = 45066] = "Z3_OP_FPA_MINUS_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_ADD"] = 45067] = "Z3_OP_FPA_ADD";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_SUB"] = 45068] = "Z3_OP_FPA_SUB";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_NEG"] = 45069] = "Z3_OP_FPA_NEG";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MUL"] = 45070] = "Z3_OP_FPA_MUL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_DIV"] = 45071] = "Z3_OP_FPA_DIV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_REM"] = 45072] = "Z3_OP_FPA_REM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_ABS"] = 45073] = "Z3_OP_FPA_ABS";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MIN"] = 45074] = "Z3_OP_FPA_MIN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_MAX"] = 45075] = "Z3_OP_FPA_MAX";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_FMA"] = 45076] = "Z3_OP_FPA_FMA";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_SQRT"] = 45077] = "Z3_OP_FPA_SQRT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_ROUND_TO_INTEGRAL"] = 45078] = "Z3_OP_FPA_ROUND_TO_INTEGRAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_EQ"] = 45079] = "Z3_OP_FPA_EQ";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_LT"] = 45080] = "Z3_OP_FPA_LT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_GT"] = 45081] = "Z3_OP_FPA_GT";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_LE"] = 45082] = "Z3_OP_FPA_LE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_GE"] = 45083] = "Z3_OP_FPA_GE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_NAN"] = 45084] = "Z3_OP_FPA_IS_NAN";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_INF"] = 45085] = "Z3_OP_FPA_IS_INF";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_ZERO"] = 45086] = "Z3_OP_FPA_IS_ZERO";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_NORMAL"] = 45087] = "Z3_OP_FPA_IS_NORMAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_SUBNORMAL"] = 45088] = "Z3_OP_FPA_IS_SUBNORMAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_NEGATIVE"] = 45089] = "Z3_OP_FPA_IS_NEGATIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_IS_POSITIVE"] = 45090] = "Z3_OP_FPA_IS_POSITIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_FP"] = 45091] = "Z3_OP_FPA_FP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_FP"] = 45092] = "Z3_OP_FPA_TO_FP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_FP_UNSIGNED"] = 45093] = "Z3_OP_FPA_TO_FP_UNSIGNED";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_UBV"] = 45094] = "Z3_OP_FPA_TO_UBV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_SBV"] = 45095] = "Z3_OP_FPA_TO_SBV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_REAL"] = 45096] = "Z3_OP_FPA_TO_REAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_TO_IEEE_BV"] = 45097] = "Z3_OP_FPA_TO_IEEE_BV";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_BVWRAP"] = 45098] = "Z3_OP_FPA_BVWRAP";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_FPA_BV2RM"] = 45099] = "Z3_OP_FPA_BV2RM";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_INTERNAL"] = 45100] = "Z3_OP_INTERNAL";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_RECURSIVE"] = 45101] = "Z3_OP_RECURSIVE";
    Z3_decl_kind[Z3_decl_kind["Z3_OP_UNINTERPRETED"] = 45102] = "Z3_OP_UNINTERPRETED";
})(Z3_decl_kind = exports.Z3_decl_kind || (exports.Z3_decl_kind = {}));
var Z3_param_kind;
(function (Z3_param_kind) {
    Z3_param_kind[Z3_param_kind["Z3_PK_UINT"] = 0] = "Z3_PK_UINT";
    Z3_param_kind[Z3_param_kind["Z3_PK_BOOL"] = 1] = "Z3_PK_BOOL";
    Z3_param_kind[Z3_param_kind["Z3_PK_DOUBLE"] = 2] = "Z3_PK_DOUBLE";
    Z3_param_kind[Z3_param_kind["Z3_PK_SYMBOL"] = 3] = "Z3_PK_SYMBOL";
    Z3_param_kind[Z3_param_kind["Z3_PK_STRING"] = 4] = "Z3_PK_STRING";
    Z3_param_kind[Z3_param_kind["Z3_PK_OTHER"] = 5] = "Z3_PK_OTHER";
    Z3_param_kind[Z3_param_kind["Z3_PK_INVALID"] = 6] = "Z3_PK_INVALID";
})(Z3_param_kind = exports.Z3_param_kind || (exports.Z3_param_kind = {}));
var Z3_ast_print_mode;
(function (Z3_ast_print_mode) {
    Z3_ast_print_mode[Z3_ast_print_mode["Z3_PRINT_SMTLIB_FULL"] = 0] = "Z3_PRINT_SMTLIB_FULL";
    Z3_ast_print_mode[Z3_ast_print_mode["Z3_PRINT_LOW_LEVEL"] = 1] = "Z3_PRINT_LOW_LEVEL";
    Z3_ast_print_mode[Z3_ast_print_mode["Z3_PRINT_SMTLIB2_COMPLIANT"] = 2] = "Z3_PRINT_SMTLIB2_COMPLIANT";
})(Z3_ast_print_mode = exports.Z3_ast_print_mode || (exports.Z3_ast_print_mode = {}));
var Z3_error_code;
(function (Z3_error_code) {
    Z3_error_code[Z3_error_code["Z3_OK"] = 0] = "Z3_OK";
    Z3_error_code[Z3_error_code["Z3_SORT_ERROR"] = 1] = "Z3_SORT_ERROR";
    Z3_error_code[Z3_error_code["Z3_IOB"] = 2] = "Z3_IOB";
    Z3_error_code[Z3_error_code["Z3_INVALID_ARG"] = 3] = "Z3_INVALID_ARG";
    Z3_error_code[Z3_error_code["Z3_PARSER_ERROR"] = 4] = "Z3_PARSER_ERROR";
    Z3_error_code[Z3_error_code["Z3_NO_PARSER"] = 5] = "Z3_NO_PARSER";
    Z3_error_code[Z3_error_code["Z3_INVALID_PATTERN"] = 6] = "Z3_INVALID_PATTERN";
    Z3_error_code[Z3_error_code["Z3_MEMOUT_FAIL"] = 7] = "Z3_MEMOUT_FAIL";
    Z3_error_code[Z3_error_code["Z3_FILE_ACCESS_ERROR"] = 8] = "Z3_FILE_ACCESS_ERROR";
    Z3_error_code[Z3_error_code["Z3_INTERNAL_FATAL"] = 9] = "Z3_INTERNAL_FATAL";
    Z3_error_code[Z3_error_code["Z3_INVALID_USAGE"] = 10] = "Z3_INVALID_USAGE";
    Z3_error_code[Z3_error_code["Z3_DEC_REF_ERROR"] = 11] = "Z3_DEC_REF_ERROR";
    Z3_error_code[Z3_error_code["Z3_EXCEPTION"] = 12] = "Z3_EXCEPTION";
})(Z3_error_code = exports.Z3_error_code || (exports.Z3_error_code = {}));
var Z3_goal_prec;
(function (Z3_goal_prec) {
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_PRECISE"] = 0] = "Z3_GOAL_PRECISE";
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_UNDER"] = 1] = "Z3_GOAL_UNDER";
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_OVER"] = 2] = "Z3_GOAL_OVER";
    Z3_goal_prec[Z3_goal_prec["Z3_GOAL_UNDER_OVER"] = 3] = "Z3_GOAL_UNDER_OVER";
})(Z3_goal_prec = exports.Z3_goal_prec || (exports.Z3_goal_prec = {}));
