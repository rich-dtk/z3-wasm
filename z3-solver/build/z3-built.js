
var initZ3 = (() => {
  var _scriptDir = typeof document !== 'undefined' && document.currentScript ? document.currentScript.src : undefined;
  if (typeof __filename !== 'undefined') _scriptDir = _scriptDir || __filename;
  return (
function(initZ3 = {})  {

// include: shell.js
// The Module object: Our interface to the outside world. We import
// and export values on it. There are various ways Module can be used:
// 1. Not defined. We create it here
// 2. A function parameter, function(Module) { ..generated code.. }
// 3. pre-run appended it, var Module = {}; ..generated code..
// 4. External script tag defines var Module.
// We need to check if Module already exists (e.g. case 3 above).
// Substitution will be replaced with actual code on later stage of the build,
// this way Closure Compiler will not mangle it (e.g. case 4. above).
// Note that if you want to run closure, and also to use Module
// after the generated code, you will need to define   var Module = {};
// before the code. Then that object will be used in the code, and you
// can continue to use Module afterwards as well.
var Module = typeof initZ3 != 'undefined' ? initZ3 : {};

// Set up the promise that indicates the Module is initialized
var readyPromiseResolve, readyPromiseReject;
Module['ready'] = new Promise(function(resolve, reject) {
  readyPromiseResolve = resolve;
  readyPromiseReject = reject;
});
["_set_throwy_error_handler","_set_noop_error_handler","_async_Z3_eval_smtlib2_string","_async_Z3_simplify","_async_Z3_simplify_ex","_async_Z3_solver_check","_async_Z3_solver_check_assumptions","_async_Z3_solver_cube","_async_Z3_solver_get_consequences","_async_Z3_tactic_apply","_async_Z3_tactic_apply_ex","_async_Z3_optimize_check","_async_Z3_algebraic_roots","_async_Z3_algebraic_eval","_async_Z3_fixedpoint_query","_async_Z3_fixedpoint_query_relations","_async_Z3_fixedpoint_query_from_lvl","_async_Z3_polynomial_subresultants","_Z3_global_param_set","_Z3_global_param_reset_all","_Z3_global_param_get","_Z3_mk_config","_Z3_del_config","_Z3_set_param_value","_Z3_mk_context","_Z3_mk_context_rc","_Z3_del_context","_Z3_inc_ref","_Z3_dec_ref","_Z3_update_param_value","_Z3_get_global_param_descrs","_Z3_interrupt","_Z3_enable_concurrent_dec_ref","_Z3_mk_params","_Z3_params_inc_ref","_Z3_params_dec_ref","_Z3_params_set_bool","_Z3_params_set_uint","_Z3_params_set_double","_Z3_params_set_symbol","_Z3_params_to_string","_Z3_params_validate","_Z3_param_descrs_inc_ref","_Z3_param_descrs_dec_ref","_Z3_param_descrs_get_kind","_Z3_param_descrs_size","_Z3_param_descrs_get_name","_Z3_param_descrs_get_documentation","_Z3_param_descrs_to_string","_Z3_mk_int_symbol","_Z3_mk_string_symbol","_Z3_mk_uninterpreted_sort","_Z3_mk_bool_sort","_Z3_mk_int_sort","_Z3_mk_real_sort","_Z3_mk_bv_sort","_Z3_mk_finite_domain_sort","_Z3_mk_array_sort","_Z3_mk_array_sort_n","_Z3_mk_tuple_sort","_Z3_mk_enumeration_sort","_Z3_mk_list_sort","_Z3_mk_constructor","_Z3_del_constructor","_Z3_mk_datatype","_Z3_mk_datatype_sort","_Z3_mk_constructor_list","_Z3_del_constructor_list","_Z3_mk_datatypes","_Z3_query_constructor","_Z3_mk_func_decl","_Z3_mk_app","_Z3_mk_const","_Z3_mk_fresh_func_decl","_Z3_mk_fresh_const","_Z3_mk_rec_func_decl","_Z3_add_rec_def","_Z3_mk_true","_Z3_mk_false","_Z3_mk_eq","_Z3_mk_distinct","_Z3_mk_not","_Z3_mk_ite","_Z3_mk_iff","_Z3_mk_implies","_Z3_mk_xor","_Z3_mk_and","_Z3_mk_or","_Z3_mk_add","_Z3_mk_mul","_Z3_mk_sub","_Z3_mk_unary_minus","_Z3_mk_div","_Z3_mk_mod","_Z3_mk_rem","_Z3_mk_power","_Z3_mk_lt","_Z3_mk_le","_Z3_mk_gt","_Z3_mk_ge","_Z3_mk_divides","_Z3_mk_int2real","_Z3_mk_real2int","_Z3_mk_is_int","_Z3_mk_bvnot","_Z3_mk_bvredand","_Z3_mk_bvredor","_Z3_mk_bvand","_Z3_mk_bvor","_Z3_mk_bvxor","_Z3_mk_bvnand","_Z3_mk_bvnor","_Z3_mk_bvxnor","_Z3_mk_bvneg","_Z3_mk_bvadd","_Z3_mk_bvsub","_Z3_mk_bvmul","_Z3_mk_bvudiv","_Z3_mk_bvsdiv","_Z3_mk_bvurem","_Z3_mk_bvsrem","_Z3_mk_bvsmod","_Z3_mk_bvult","_Z3_mk_bvslt","_Z3_mk_bvule","_Z3_mk_bvsle","_Z3_mk_bvuge","_Z3_mk_bvsge","_Z3_mk_bvugt","_Z3_mk_bvsgt","_Z3_mk_concat","_Z3_mk_extract","_Z3_mk_sign_ext","_Z3_mk_zero_ext","_Z3_mk_repeat","_Z3_mk_bit2bool","_Z3_mk_bvshl","_Z3_mk_bvlshr","_Z3_mk_bvashr","_Z3_mk_rotate_left","_Z3_mk_rotate_right","_Z3_mk_ext_rotate_left","_Z3_mk_ext_rotate_right","_Z3_mk_int2bv","_Z3_mk_bv2int","_Z3_mk_bvadd_no_overflow","_Z3_mk_bvadd_no_underflow","_Z3_mk_bvsub_no_overflow","_Z3_mk_bvsub_no_underflow","_Z3_mk_bvsdiv_no_overflow","_Z3_mk_bvneg_no_overflow","_Z3_mk_bvmul_no_overflow","_Z3_mk_bvmul_no_underflow","_Z3_mk_select","_Z3_mk_select_n","_Z3_mk_store","_Z3_mk_store_n","_Z3_mk_const_array","_Z3_mk_map","_Z3_mk_array_default","_Z3_mk_as_array","_Z3_mk_set_has_size","_Z3_mk_set_sort","_Z3_mk_empty_set","_Z3_mk_full_set","_Z3_mk_set_add","_Z3_mk_set_del","_Z3_mk_set_union","_Z3_mk_set_intersect","_Z3_mk_set_difference","_Z3_mk_set_complement","_Z3_mk_set_member","_Z3_mk_set_subset","_Z3_mk_array_ext","_Z3_mk_numeral","_Z3_mk_real","_Z3_mk_real_int64","_Z3_mk_int","_Z3_mk_unsigned_int","_Z3_mk_int64","_Z3_mk_unsigned_int64","_Z3_mk_bv_numeral","_Z3_mk_seq_sort","_Z3_is_seq_sort","_Z3_get_seq_sort_basis","_Z3_mk_re_sort","_Z3_is_re_sort","_Z3_get_re_sort_basis","_Z3_mk_string_sort","_Z3_mk_char_sort","_Z3_is_string_sort","_Z3_is_char_sort","_Z3_mk_string","_Z3_mk_lstring","_Z3_mk_u32string","_Z3_is_string","_Z3_get_string","_Z3_get_lstring","_Z3_get_string_length","_Z3_get_string_contents","_Z3_mk_seq_empty","_Z3_mk_seq_unit","_Z3_mk_seq_concat","_Z3_mk_seq_prefix","_Z3_mk_seq_suffix","_Z3_mk_seq_contains","_Z3_mk_str_lt","_Z3_mk_str_le","_Z3_mk_seq_extract","_Z3_mk_seq_replace","_Z3_mk_seq_at","_Z3_mk_seq_nth","_Z3_mk_seq_length","_Z3_mk_seq_index","_Z3_mk_seq_last_index","_Z3_mk_str_to_int","_Z3_mk_int_to_str","_Z3_mk_string_to_code","_Z3_mk_string_from_code","_Z3_mk_ubv_to_str","_Z3_mk_sbv_to_str","_Z3_mk_seq_to_re","_Z3_mk_seq_in_re","_Z3_mk_re_plus","_Z3_mk_re_star","_Z3_mk_re_option","_Z3_mk_re_union","_Z3_mk_re_concat","_Z3_mk_re_range","_Z3_mk_re_allchar","_Z3_mk_re_loop","_Z3_mk_re_power","_Z3_mk_re_intersect","_Z3_mk_re_complement","_Z3_mk_re_diff","_Z3_mk_re_empty","_Z3_mk_re_full","_Z3_mk_char","_Z3_mk_char_le","_Z3_mk_char_to_int","_Z3_mk_char_to_bv","_Z3_mk_char_from_bv","_Z3_mk_char_is_digit","_Z3_mk_linear_order","_Z3_mk_partial_order","_Z3_mk_piecewise_linear_order","_Z3_mk_tree_order","_Z3_mk_transitive_closure","_Z3_mk_pattern","_Z3_mk_bound","_Z3_mk_forall","_Z3_mk_exists","_Z3_mk_quantifier","_Z3_mk_quantifier_ex","_Z3_mk_forall_const","_Z3_mk_exists_const","_Z3_mk_quantifier_const","_Z3_mk_quantifier_const_ex","_Z3_mk_lambda","_Z3_mk_lambda_const","_Z3_get_symbol_kind","_Z3_get_symbol_int","_Z3_get_symbol_string","_Z3_get_sort_name","_Z3_get_sort_id","_Z3_sort_to_ast","_Z3_is_eq_sort","_Z3_get_sort_kind","_Z3_get_bv_sort_size","_Z3_get_finite_domain_sort_size","_Z3_get_array_sort_domain","_Z3_get_array_sort_domain_n","_Z3_get_array_sort_range","_Z3_get_tuple_sort_mk_decl","_Z3_get_tuple_sort_num_fields","_Z3_get_tuple_sort_field_decl","_Z3_get_datatype_sort_num_constructors","_Z3_get_datatype_sort_constructor","_Z3_get_datatype_sort_recognizer","_Z3_get_datatype_sort_constructor_accessor","_Z3_datatype_update_field","_Z3_get_relation_arity","_Z3_get_relation_column","_Z3_mk_atmost","_Z3_mk_atleast","_Z3_mk_pble","_Z3_mk_pbge","_Z3_mk_pbeq","_Z3_func_decl_to_ast","_Z3_is_eq_func_decl","_Z3_get_func_decl_id","_Z3_get_decl_name","_Z3_get_decl_kind","_Z3_get_domain_size","_Z3_get_arity","_Z3_get_domain","_Z3_get_range","_Z3_get_decl_num_parameters","_Z3_get_decl_parameter_kind","_Z3_get_decl_int_parameter","_Z3_get_decl_double_parameter","_Z3_get_decl_symbol_parameter","_Z3_get_decl_sort_parameter","_Z3_get_decl_ast_parameter","_Z3_get_decl_func_decl_parameter","_Z3_get_decl_rational_parameter","_Z3_app_to_ast","_Z3_get_app_decl","_Z3_get_app_num_args","_Z3_get_app_arg","_Z3_is_eq_ast","_Z3_get_ast_id","_Z3_get_ast_hash","_Z3_get_sort","_Z3_is_well_sorted","_Z3_get_bool_value","_Z3_get_ast_kind","_Z3_is_app","_Z3_is_numeral_ast","_Z3_is_algebraic_number","_Z3_to_app","_Z3_to_func_decl","_Z3_get_numeral_string","_Z3_get_numeral_binary_string","_Z3_get_numeral_decimal_string","_Z3_get_numeral_double","_Z3_get_numerator","_Z3_get_denominator","_Z3_get_numeral_small","_Z3_get_numeral_int","_Z3_get_numeral_uint","_Z3_get_numeral_uint64","_Z3_get_numeral_int64","_Z3_get_numeral_rational_int64","_Z3_get_algebraic_number_lower","_Z3_get_algebraic_number_upper","_Z3_pattern_to_ast","_Z3_get_pattern_num_terms","_Z3_get_pattern","_Z3_get_index_value","_Z3_is_quantifier_forall","_Z3_is_quantifier_exists","_Z3_is_lambda","_Z3_get_quantifier_weight","_Z3_get_quantifier_num_patterns","_Z3_get_quantifier_pattern_ast","_Z3_get_quantifier_num_no_patterns","_Z3_get_quantifier_no_pattern_ast","_Z3_get_quantifier_num_bound","_Z3_get_quantifier_bound_name","_Z3_get_quantifier_bound_sort","_Z3_get_quantifier_body","_Z3_simplify","_Z3_simplify_ex","_Z3_simplify_get_help","_Z3_simplify_get_param_descrs","_Z3_update_term","_Z3_substitute","_Z3_substitute_vars","_Z3_substitute_funs","_Z3_translate","_Z3_mk_model","_Z3_model_inc_ref","_Z3_model_dec_ref","_Z3_model_eval","_Z3_model_get_const_interp","_Z3_model_has_interp","_Z3_model_get_func_interp","_Z3_model_get_num_consts","_Z3_model_get_const_decl","_Z3_model_get_num_funcs","_Z3_model_get_func_decl","_Z3_model_get_num_sorts","_Z3_model_get_sort","_Z3_model_get_sort_universe","_Z3_model_translate","_Z3_is_as_array","_Z3_get_as_array_func_decl","_Z3_add_func_interp","_Z3_add_const_interp","_Z3_func_interp_inc_ref","_Z3_func_interp_dec_ref","_Z3_func_interp_get_num_entries","_Z3_func_interp_get_entry","_Z3_func_interp_get_else","_Z3_func_interp_set_else","_Z3_func_interp_get_arity","_Z3_func_interp_add_entry","_Z3_func_entry_inc_ref","_Z3_func_entry_dec_ref","_Z3_func_entry_get_value","_Z3_func_entry_get_num_args","_Z3_func_entry_get_arg","_Z3_open_log","_Z3_append_log","_Z3_close_log","_Z3_toggle_warning_messages","_Z3_set_ast_print_mode","_Z3_ast_to_string","_Z3_pattern_to_string","_Z3_sort_to_string","_Z3_func_decl_to_string","_Z3_model_to_string","_Z3_benchmark_to_smtlib_string","_Z3_parse_smtlib2_string","_Z3_parse_smtlib2_file","_Z3_eval_smtlib2_string","_Z3_mk_parser_context","_Z3_parser_context_inc_ref","_Z3_parser_context_dec_ref","_Z3_parser_context_add_sort","_Z3_parser_context_add_decl","_Z3_parser_context_from_string","_Z3_get_error_code","_Z3_set_error","_Z3_get_error_msg","_Z3_get_version","_Z3_get_full_version","_Z3_enable_trace","_Z3_disable_trace","_Z3_reset_memory","_Z3_finalize_memory","_Z3_mk_goal","_Z3_goal_inc_ref","_Z3_goal_dec_ref","_Z3_goal_precision","_Z3_goal_assert","_Z3_goal_inconsistent","_Z3_goal_depth","_Z3_goal_reset","_Z3_goal_size","_Z3_goal_formula","_Z3_goal_num_exprs","_Z3_goal_is_decided_sat","_Z3_goal_is_decided_unsat","_Z3_goal_translate","_Z3_goal_convert_model","_Z3_goal_to_string","_Z3_goal_to_dimacs_string","_Z3_mk_tactic","_Z3_tactic_inc_ref","_Z3_tactic_dec_ref","_Z3_mk_probe","_Z3_probe_inc_ref","_Z3_probe_dec_ref","_Z3_tactic_and_then","_Z3_tactic_or_else","_Z3_tactic_par_or","_Z3_tactic_par_and_then","_Z3_tactic_try_for","_Z3_tactic_when","_Z3_tactic_cond","_Z3_tactic_repeat","_Z3_tactic_skip","_Z3_tactic_fail","_Z3_tactic_fail_if","_Z3_tactic_fail_if_not_decided","_Z3_tactic_using_params","_Z3_mk_simplifier","_Z3_simplifier_inc_ref","_Z3_simplifier_dec_ref","_Z3_solver_add_simplifier","_Z3_simplifier_and_then","_Z3_simplifier_using_params","_Z3_get_num_simplifiers","_Z3_get_simplifier_name","_Z3_simplifier_get_help","_Z3_simplifier_get_param_descrs","_Z3_simplifier_get_descr","_Z3_probe_const","_Z3_probe_lt","_Z3_probe_gt","_Z3_probe_le","_Z3_probe_ge","_Z3_probe_eq","_Z3_probe_and","_Z3_probe_or","_Z3_probe_not","_Z3_get_num_tactics","_Z3_get_tactic_name","_Z3_get_num_probes","_Z3_get_probe_name","_Z3_tactic_get_help","_Z3_tactic_get_param_descrs","_Z3_tactic_get_descr","_Z3_probe_get_descr","_Z3_probe_apply","_Z3_tactic_apply","_Z3_tactic_apply_ex","_Z3_apply_result_inc_ref","_Z3_apply_result_dec_ref","_Z3_apply_result_to_string","_Z3_apply_result_get_num_subgoals","_Z3_apply_result_get_subgoal","_Z3_mk_solver","_Z3_mk_simple_solver","_Z3_mk_solver_for_logic","_Z3_mk_solver_from_tactic","_Z3_solver_translate","_Z3_solver_import_model_converter","_Z3_solver_get_help","_Z3_solver_get_param_descrs","_Z3_solver_set_params","_Z3_solver_inc_ref","_Z3_solver_dec_ref","_Z3_solver_interrupt","_Z3_solver_push","_Z3_solver_pop","_Z3_solver_reset","_Z3_solver_get_num_scopes","_Z3_solver_assert","_Z3_solver_assert_and_track","_Z3_solver_from_file","_Z3_solver_from_string","_Z3_solver_get_assertions","_Z3_solver_get_units","_Z3_solver_get_trail","_Z3_solver_get_non_units","_Z3_solver_get_levels","_Z3_solver_congruence_root","_Z3_solver_congruence_next","_Z3_solver_register_on_clause","_Z3_solver_propagate_init","_Z3_solver_propagate_fixed","_Z3_solver_propagate_final","_Z3_solver_propagate_eq","_Z3_solver_propagate_diseq","_Z3_solver_propagate_created","_Z3_solver_propagate_decide","_Z3_solver_next_split","_Z3_solver_propagate_declare","_Z3_solver_propagate_register","_Z3_solver_propagate_register_cb","_Z3_solver_propagate_consequence","_Z3_solver_check","_Z3_solver_check_assumptions","_Z3_get_implied_equalities","_Z3_solver_get_consequences","_Z3_solver_cube","_Z3_solver_get_model","_Z3_solver_get_proof","_Z3_solver_get_unsat_core","_Z3_solver_get_reason_unknown","_Z3_solver_get_statistics","_Z3_solver_to_string","_Z3_solver_to_dimacs_string","_Z3_stats_to_string","_Z3_stats_inc_ref","_Z3_stats_dec_ref","_Z3_stats_size","_Z3_stats_get_key","_Z3_stats_is_uint","_Z3_stats_is_double","_Z3_stats_get_uint_value","_Z3_stats_get_double_value","_Z3_get_estimated_alloc_size","_Z3_algebraic_is_value","_Z3_algebraic_is_pos","_Z3_algebraic_is_neg","_Z3_algebraic_is_zero","_Z3_algebraic_sign","_Z3_algebraic_add","_Z3_algebraic_sub","_Z3_algebraic_mul","_Z3_algebraic_div","_Z3_algebraic_root","_Z3_algebraic_power","_Z3_algebraic_lt","_Z3_algebraic_gt","_Z3_algebraic_le","_Z3_algebraic_ge","_Z3_algebraic_eq","_Z3_algebraic_neq","_Z3_algebraic_roots","_Z3_algebraic_eval","_Z3_algebraic_get_poly","_Z3_algebraic_get_i","_Z3_mk_ast_vector","_Z3_ast_vector_inc_ref","_Z3_ast_vector_dec_ref","_Z3_ast_vector_size","_Z3_ast_vector_get","_Z3_ast_vector_set","_Z3_ast_vector_resize","_Z3_ast_vector_push","_Z3_ast_vector_translate","_Z3_ast_vector_to_string","_Z3_mk_ast_map","_Z3_ast_map_inc_ref","_Z3_ast_map_dec_ref","_Z3_ast_map_contains","_Z3_ast_map_find","_Z3_ast_map_insert","_Z3_ast_map_erase","_Z3_ast_map_reset","_Z3_ast_map_size","_Z3_ast_map_keys","_Z3_ast_map_to_string","_Z3_mk_fixedpoint","_Z3_fixedpoint_inc_ref","_Z3_fixedpoint_dec_ref","_Z3_fixedpoint_add_rule","_Z3_fixedpoint_add_fact","_Z3_fixedpoint_assert","_Z3_fixedpoint_query","_Z3_fixedpoint_query_relations","_Z3_fixedpoint_get_answer","_Z3_fixedpoint_get_reason_unknown","_Z3_fixedpoint_update_rule","_Z3_fixedpoint_get_num_levels","_Z3_fixedpoint_get_cover_delta","_Z3_fixedpoint_add_cover","_Z3_fixedpoint_get_statistics","_Z3_fixedpoint_register_relation","_Z3_fixedpoint_set_predicate_representation","_Z3_fixedpoint_get_rules","_Z3_fixedpoint_get_assertions","_Z3_fixedpoint_set_params","_Z3_fixedpoint_get_help","_Z3_fixedpoint_get_param_descrs","_Z3_fixedpoint_to_string","_Z3_fixedpoint_from_string","_Z3_fixedpoint_from_file","_Z3_mk_fpa_rounding_mode_sort","_Z3_mk_fpa_round_nearest_ties_to_even","_Z3_mk_fpa_rne","_Z3_mk_fpa_round_nearest_ties_to_away","_Z3_mk_fpa_rna","_Z3_mk_fpa_round_toward_positive","_Z3_mk_fpa_rtp","_Z3_mk_fpa_round_toward_negative","_Z3_mk_fpa_rtn","_Z3_mk_fpa_round_toward_zero","_Z3_mk_fpa_rtz","_Z3_mk_fpa_sort","_Z3_mk_fpa_sort_half","_Z3_mk_fpa_sort_16","_Z3_mk_fpa_sort_single","_Z3_mk_fpa_sort_32","_Z3_mk_fpa_sort_double","_Z3_mk_fpa_sort_64","_Z3_mk_fpa_sort_quadruple","_Z3_mk_fpa_sort_128","_Z3_mk_fpa_nan","_Z3_mk_fpa_inf","_Z3_mk_fpa_zero","_Z3_mk_fpa_fp","_Z3_mk_fpa_numeral_float","_Z3_mk_fpa_numeral_double","_Z3_mk_fpa_numeral_int","_Z3_mk_fpa_numeral_int_uint","_Z3_mk_fpa_numeral_int64_uint64","_Z3_mk_fpa_abs","_Z3_mk_fpa_neg","_Z3_mk_fpa_add","_Z3_mk_fpa_sub","_Z3_mk_fpa_mul","_Z3_mk_fpa_div","_Z3_mk_fpa_fma","_Z3_mk_fpa_sqrt","_Z3_mk_fpa_rem","_Z3_mk_fpa_round_to_integral","_Z3_mk_fpa_min","_Z3_mk_fpa_max","_Z3_mk_fpa_leq","_Z3_mk_fpa_lt","_Z3_mk_fpa_geq","_Z3_mk_fpa_gt","_Z3_mk_fpa_eq","_Z3_mk_fpa_is_normal","_Z3_mk_fpa_is_subnormal","_Z3_mk_fpa_is_zero","_Z3_mk_fpa_is_infinite","_Z3_mk_fpa_is_nan","_Z3_mk_fpa_is_negative","_Z3_mk_fpa_is_positive","_Z3_mk_fpa_to_fp_bv","_Z3_mk_fpa_to_fp_float","_Z3_mk_fpa_to_fp_real","_Z3_mk_fpa_to_fp_signed","_Z3_mk_fpa_to_fp_unsigned","_Z3_mk_fpa_to_ubv","_Z3_mk_fpa_to_sbv","_Z3_mk_fpa_to_real","_Z3_fpa_get_ebits","_Z3_fpa_get_sbits","_Z3_fpa_is_numeral_nan","_Z3_fpa_is_numeral_inf","_Z3_fpa_is_numeral_zero","_Z3_fpa_is_numeral_normal","_Z3_fpa_is_numeral_subnormal","_Z3_fpa_is_numeral_positive","_Z3_fpa_is_numeral_negative","_Z3_fpa_get_numeral_sign_bv","_Z3_fpa_get_numeral_significand_bv","_Z3_fpa_get_numeral_sign","_Z3_fpa_get_numeral_significand_string","_Z3_fpa_get_numeral_significand_uint64","_Z3_fpa_get_numeral_exponent_string","_Z3_fpa_get_numeral_exponent_int64","_Z3_fpa_get_numeral_exponent_bv","_Z3_mk_fpa_to_ieee_bv","_Z3_mk_fpa_to_fp_int_real","_Z3_mk_optimize","_Z3_optimize_inc_ref","_Z3_optimize_dec_ref","_Z3_optimize_assert","_Z3_optimize_assert_and_track","_Z3_optimize_assert_soft","_Z3_optimize_maximize","_Z3_optimize_minimize","_Z3_optimize_push","_Z3_optimize_pop","_Z3_optimize_check","_Z3_optimize_get_reason_unknown","_Z3_optimize_get_model","_Z3_optimize_get_unsat_core","_Z3_optimize_set_params","_Z3_optimize_get_param_descrs","_Z3_optimize_get_lower","_Z3_optimize_get_upper","_Z3_optimize_get_lower_as_vector","_Z3_optimize_get_upper_as_vector","_Z3_optimize_to_string","_Z3_optimize_from_string","_Z3_optimize_from_file","_Z3_optimize_get_help","_Z3_optimize_get_statistics","_Z3_optimize_get_assertions","_Z3_optimize_get_objectives","_Z3_polynomial_subresultants","_Z3_rcf_del","_Z3_rcf_mk_rational","_Z3_rcf_mk_small_int","_Z3_rcf_mk_pi","_Z3_rcf_mk_e","_Z3_rcf_mk_infinitesimal","_Z3_rcf_mk_roots","_Z3_rcf_add","_Z3_rcf_sub","_Z3_rcf_mul","_Z3_rcf_div","_Z3_rcf_neg","_Z3_rcf_inv","_Z3_rcf_power","_Z3_rcf_lt","_Z3_rcf_gt","_Z3_rcf_le","_Z3_rcf_ge","_Z3_rcf_eq","_Z3_rcf_neq","_Z3_rcf_num_to_string","_Z3_rcf_num_to_decimal_string","_Z3_rcf_get_numerator_denominator","_Z3_fixedpoint_query_from_lvl","_Z3_fixedpoint_get_ground_sat_answer","_Z3_fixedpoint_get_rules_along_trace","_Z3_fixedpoint_get_rule_names_along_trace","_Z3_fixedpoint_add_invariant","_Z3_fixedpoint_get_reachable","_Z3_qe_model_project","_Z3_qe_model_project_skolem","_Z3_model_extrapolate","_Z3_qe_lite","__emscripten_thread_init","__emscripten_thread_exit","__emscripten_thread_crashed","__emscripten_tls_init","_pthread_self","executeNotifiedProxyingQueue","establishStackSpace","invokeEntryPoint","PThread","getExceptionMessage","___get_exception_message","_free","_fflush","__emscripten_proxy_execute_task_queue","onRuntimeInitialized"].forEach((prop) => {
  if (!Object.getOwnPropertyDescriptor(Module['ready'], prop)) {
    Object.defineProperty(Module['ready'], prop, {
      get: () => abort('You are getting ' + prop + ' on the Promise object, instead of the instance. Use .then() to get called back with the instance, see the MODULARIZE docs in src/settings.js'),
      set: () => abort('You are setting ' + prop + ' on the Promise object, instead of the instance. Use .then() to get called back with the instance, see the MODULARIZE docs in src/settings.js'),
    });
  }
});

// --pre-jses are emitted after the Module integration code, so that they can
// refer to Module (if they choose; they can also define Module)
// this wrapper works with async-fns to provide promise-based off-thread versions of some functions
// It's prepended directly by emscripten to the resulting z3-built.js

let capability = null;
function resolve_async(val) {
  // setTimeout is a workaround for https://github.com/emscripten-core/emscripten/issues/15900
  if (capability == null) {
    return;
  }
  let cap = capability;
  capability = null;

  setTimeout(() => {
    cap.resolve(val);
  }, 0);
}

function reject_async(val) {
  if (capability == null) {
    return;
  }
  let cap = capability;
  capability = null;

  setTimeout(() => {
    cap.reject(val);
  }, 0);
}

Module.async_call = function (f, ...args) {
  if (capability !== null) {
    throw new Error(`you can't execute multiple async functions at the same time; let the previous one finish first`);
  }
  let promise = new Promise((resolve, reject) => {
    capability = { resolve, reject };
  });
  f(...args);
  return promise;
};



// Sometimes an existing Module object exists with properties
// meant to overwrite the default module functionality. Here
// we collect those properties and reapply _after_ we configure
// the current environment's defaults to avoid having to be so
// defensive during initialization.
var moduleOverrides = Object.assign({}, Module);

var arguments_ = [];
var thisProgram = './this.program';
var quit_ = (status, toThrow) => {
  throw toThrow;
};

// Determine the runtime environment we are in. You can customize this by
// setting the ENVIRONMENT setting at compile time (see settings.js).

// Attempt to auto-detect the environment
var ENVIRONMENT_IS_WEB = typeof window == 'object';
var ENVIRONMENT_IS_WORKER = typeof importScripts == 'function';
// N.b. Electron.js environment is simultaneously a NODE-environment, but
// also a web environment.
var ENVIRONMENT_IS_NODE = typeof process == 'object' && typeof process.versions == 'object' && typeof process.versions.node == 'string';
var ENVIRONMENT_IS_SHELL = !ENVIRONMENT_IS_WEB && !ENVIRONMENT_IS_NODE && !ENVIRONMENT_IS_WORKER;

if (Module['ENVIRONMENT']) {
  throw new Error('Module.ENVIRONMENT has been deprecated. To force the environment, use the ENVIRONMENT compile-time option (for example, -sENVIRONMENT=web or -sENVIRONMENT=node)');
}

// Three configurations we can be running in:
// 1) We could be the application main() thread running in the main JS UI thread. (ENVIRONMENT_IS_WORKER == false and ENVIRONMENT_IS_PTHREAD == false)
// 2) We could be the application main() thread proxied to worker. (with Emscripten -sPROXY_TO_WORKER) (ENVIRONMENT_IS_WORKER == true, ENVIRONMENT_IS_PTHREAD == false)
// 3) We could be an application pthread running in a worker. (ENVIRONMENT_IS_WORKER == true and ENVIRONMENT_IS_PTHREAD == true)

// ENVIRONMENT_IS_PTHREAD=true will have been preset in worker.js. Make it false in the main runtime thread.
var ENVIRONMENT_IS_PTHREAD = Module['ENVIRONMENT_IS_PTHREAD'] || false;

// `/` should be present at the end if `scriptDirectory` is not empty
var scriptDirectory = '';
function locateFile(path) {
  if (Module['locateFile']) {
    return Module['locateFile'](path, scriptDirectory);
  }
  return scriptDirectory + path;
}

// Hooks that are implemented differently in different runtime environments.
var read_,
    readAsync,
    readBinary,
    setWindowTitle;

// Normally we don't log exceptions but instead let them bubble out the top
// level where the embedding environment (e.g. the browser) can handle
// them.
// However under v8 and node we sometimes exit the process direcly in which case
// its up to use us to log the exception before exiting.
// If we fix https://github.com/emscripten-core/emscripten/issues/15080
// this may no longer be needed under node.
function logExceptionOnExit(e) {
  if (e instanceof ExitStatus) return;
  let toLog = e;
  if (e && typeof e == 'object' && e.stack) {
    toLog = [e, e.stack];
  }
  err('exiting due to exception: ' + toLog);
}

if (ENVIRONMENT_IS_NODE) {
  if (typeof process == 'undefined' || !process.release || process.release.name !== 'node') throw new Error('not compiled for this environment (did you build to HTML and try to run it not on the web, or set ENVIRONMENT to something - like node - and run it someplace else - like on the web?)');
  // `require()` is no-op in an ESM module, use `createRequire()` to construct
  // the require()` function.  This is only necessary for multi-environment
  // builds, `-sENVIRONMENT=node` emits a static import declaration instead.
  // TODO: Swap all `require()`'s with `import()`'s?
  // These modules will usually be used on Node.js. Load them eagerly to avoid
  // the complexity of lazy-loading.
  var fs = require('fs');
  var nodePath = require('path');

  if (ENVIRONMENT_IS_WORKER) {
    scriptDirectory = nodePath.dirname(scriptDirectory) + '/';
  } else {
    scriptDirectory = __dirname + '/';
  }

// include: node_shell_read.js
read_ = (filename, binary) => {
  // We need to re-wrap `file://` strings to URLs. Normalizing isn't
  // necessary in that case, the path should already be absolute.
  filename = isFileURI(filename) ? new URL(filename) : nodePath.normalize(filename);
  return fs.readFileSync(filename, binary ? undefined : 'utf8');
};

readBinary = (filename) => {
  var ret = read_(filename, true);
  if (!ret.buffer) {
    ret = new Uint8Array(ret);
  }
  assert(ret.buffer);
  return ret;
};

readAsync = (filename, onload, onerror) => {
  // See the comment in the `read_` function.
  filename = isFileURI(filename) ? new URL(filename) : nodePath.normalize(filename);
  fs.readFile(filename, function(err, data) {
    if (err) onerror(err);
    else onload(data.buffer);
  });
};

// end include: node_shell_read.js
  if (process.argv.length > 1) {
    thisProgram = process.argv[1].replace(/\\/g, '/');
  }

  arguments_ = process.argv.slice(2);

  // MODULARIZE will export the module in the proper place outside, we don't need to export here

  process.on('uncaughtException', function(ex) {
    // suppress ExitStatus exceptions from showing an error
    if (!(ex instanceof ExitStatus)) {
      throw ex;
    }
  });

  // Without this older versions of node (< v15) will log unhandled rejections
  // but return 0, which is not normally the desired behaviour.  This is
  // not be needed with node v15 and about because it is now the default
  // behaviour:
  // See https://nodejs.org/api/cli.html#cli_unhandled_rejections_mode
  var nodeMajor = process.versions.node.split(".")[0];
  if (nodeMajor < 15) {
    process.on('unhandledRejection', function(reason) { throw reason; });
  }

  quit_ = (status, toThrow) => {
    if (keepRuntimeAlive()) {
      process.exitCode = status;
      throw toThrow;
    }
    logExceptionOnExit(toThrow);
    process.exit(status);
  };

  Module['inspect'] = function () { return '[Emscripten Module object]'; };

  let nodeWorkerThreads;
  try {
    nodeWorkerThreads = require('worker_threads');
  } catch (e) {
    console.error('The "worker_threads" module is not supported in this node.js build - perhaps a newer version is needed?');
    throw e;
  }
  global.Worker = nodeWorkerThreads.Worker;

} else
if (ENVIRONMENT_IS_SHELL) {

  if ((typeof process == 'object' && typeof require === 'function') || typeof window == 'object' || typeof importScripts == 'function') throw new Error('not compiled for this environment (did you build to HTML and try to run it not on the web, or set ENVIRONMENT to something - like node - and run it someplace else - like on the web?)');

  if (typeof read != 'undefined') {
    read_ = function shell_read(f) {
      return read(f);
    };
  }

  readBinary = function readBinary(f) {
    let data;
    if (typeof readbuffer == 'function') {
      return new Uint8Array(readbuffer(f));
    }
    data = read(f, 'binary');
    assert(typeof data == 'object');
    return data;
  };

  readAsync = function readAsync(f, onload, onerror) {
    setTimeout(() => onload(readBinary(f)), 0);
  };

  if (typeof clearTimeout == 'undefined') {
    globalThis.clearTimeout = (id) => {};
  }

  if (typeof scriptArgs != 'undefined') {
    arguments_ = scriptArgs;
  } else if (typeof arguments != 'undefined') {
    arguments_ = arguments;
  }

  if (typeof quit == 'function') {
    quit_ = (status, toThrow) => {
      logExceptionOnExit(toThrow);
      quit(status);
    };
  }

  if (typeof print != 'undefined') {
    // Prefer to use print/printErr where they exist, as they usually work better.
    if (typeof console == 'undefined') console = /** @type{!Console} */({});
    console.log = /** @type{!function(this:Console, ...*): undefined} */ (print);
    console.warn = console.error = /** @type{!function(this:Console, ...*): undefined} */ (typeof printErr != 'undefined' ? printErr : print);
  }

} else

// Note that this includes Node.js workers when relevant (pthreads is enabled).
// Node.js workers are detected as a combination of ENVIRONMENT_IS_WORKER and
// ENVIRONMENT_IS_NODE.
if (ENVIRONMENT_IS_WEB || ENVIRONMENT_IS_WORKER) {
  if (ENVIRONMENT_IS_WORKER) { // Check worker, not web, since window could be polyfilled
    scriptDirectory = self.location.href;
  } else if (typeof document != 'undefined' && document.currentScript) { // web
    scriptDirectory = document.currentScript.src;
  }
  // When MODULARIZE, this JS may be executed later, after document.currentScript
  // is gone, so we saved it, and we use it here instead of any other info.
  if (_scriptDir) {
    scriptDirectory = _scriptDir;
  }
  // blob urls look like blob:http://site.com/etc/etc and we cannot infer anything from them.
  // otherwise, slice off the final part of the url to find the script directory.
  // if scriptDirectory does not contain a slash, lastIndexOf will return -1,
  // and scriptDirectory will correctly be replaced with an empty string.
  // If scriptDirectory contains a query (starting with ?) or a fragment (starting with #),
  // they are removed because they could contain a slash.
  if (scriptDirectory.indexOf('blob:') !== 0) {
    scriptDirectory = scriptDirectory.substr(0, scriptDirectory.replace(/[?#].*/, "").lastIndexOf('/')+1);
  } else {
    scriptDirectory = '';
  }

  if (!(typeof window == 'object' || typeof importScripts == 'function')) throw new Error('not compiled for this environment (did you build to HTML and try to run it not on the web, or set ENVIRONMENT to something - like node - and run it someplace else - like on the web?)');

  // Differentiate the Web Worker from the Node Worker case, as reading must
  // be done differently.
  if (!ENVIRONMENT_IS_NODE)
  {
// include: web_or_worker_shell_read.js
read_ = (url) => {
      var xhr = new XMLHttpRequest();
      xhr.open('GET', url, false);
      xhr.send(null);
      return xhr.responseText;
  }

  if (ENVIRONMENT_IS_WORKER) {
    readBinary = (url) => {
        var xhr = new XMLHttpRequest();
        xhr.open('GET', url, false);
        xhr.responseType = 'arraybuffer';
        xhr.send(null);
        return new Uint8Array(/** @type{!ArrayBuffer} */(xhr.response));
    };
  }

  readAsync = (url, onload, onerror) => {
    var xhr = new XMLHttpRequest();
    xhr.open('GET', url, true);
    xhr.responseType = 'arraybuffer';
    xhr.onload = () => {
      if (xhr.status == 200 || (xhr.status == 0 && xhr.response)) { // file URLs can return 0
        onload(xhr.response);
        return;
      }
      onerror();
    };
    xhr.onerror = onerror;
    xhr.send(null);
  }

// end include: web_or_worker_shell_read.js
  }

  setWindowTitle = (title) => document.title = title;
} else
{
  throw new Error('environment detection error');
}

if (ENVIRONMENT_IS_NODE) {
  // Polyfill the performance object, which emscripten pthreads support
  // depends on for good timing.
  if (typeof performance == 'undefined') {
    global.performance = require('perf_hooks').performance;
  }
}

// Set up the out() and err() hooks, which are how we can print to stdout or
// stderr, respectively.
// Normally just binding console.log/console.warn here works fine, but
// under node (with workers) we see missing/out-of-order messages so route
// directly to stdout and stderr.
// See https://github.com/emscripten-core/emscripten/issues/14804
var defaultPrint = console.log.bind(console);
var defaultPrintErr = console.warn.bind(console);
if (ENVIRONMENT_IS_NODE) {
  defaultPrint = (str) => fs.writeSync(1, str + '\n');
  defaultPrintErr = (str) => fs.writeSync(2, str + '\n');
}
var out = Module['print'] || defaultPrint;
var err = Module['printErr'] || defaultPrintErr;

// Merge back in the overrides
Object.assign(Module, moduleOverrides);
// Free the object hierarchy contained in the overrides, this lets the GC
// reclaim data used e.g. in memoryInitializerRequest, which is a large typed array.
moduleOverrides = null;
checkIncomingModuleAPI();

// Emit code to handle expected values on the Module object. This applies Module.x
// to the proper local x. This has two benefits: first, we only emit it if it is
// expected to arrive, and second, by using a local everywhere else that can be
// minified.

if (Module['arguments']) arguments_ = Module['arguments'];legacyModuleProp('arguments', 'arguments_');

if (Module['thisProgram']) thisProgram = Module['thisProgram'];legacyModuleProp('thisProgram', 'thisProgram');

if (Module['quit']) quit_ = Module['quit'];legacyModuleProp('quit', 'quit_');

// perform assertions in shell.js after we set up out() and err(), as otherwise if an assertion fails it cannot print the message
// Assertions on removed incoming Module JS APIs.
assert(typeof Module['memoryInitializerPrefixURL'] == 'undefined', 'Module.memoryInitializerPrefixURL option was removed, use Module.locateFile instead');
assert(typeof Module['pthreadMainPrefixURL'] == 'undefined', 'Module.pthreadMainPrefixURL option was removed, use Module.locateFile instead');
assert(typeof Module['cdInitializerPrefixURL'] == 'undefined', 'Module.cdInitializerPrefixURL option was removed, use Module.locateFile instead');
assert(typeof Module['filePackagePrefixURL'] == 'undefined', 'Module.filePackagePrefixURL option was removed, use Module.locateFile instead');
assert(typeof Module['read'] == 'undefined', 'Module.read option was removed (modify read_ in JS)');
assert(typeof Module['readAsync'] == 'undefined', 'Module.readAsync option was removed (modify readAsync in JS)');
assert(typeof Module['readBinary'] == 'undefined', 'Module.readBinary option was removed (modify readBinary in JS)');
assert(typeof Module['setWindowTitle'] == 'undefined', 'Module.setWindowTitle option was removed (modify setWindowTitle in JS)');
assert(typeof Module['TOTAL_MEMORY'] == 'undefined', 'Module.TOTAL_MEMORY has been renamed Module.INITIAL_MEMORY');
legacyModuleProp('read', 'read_');
legacyModuleProp('readAsync', 'readAsync');
legacyModuleProp('readBinary', 'readBinary');
legacyModuleProp('setWindowTitle', 'setWindowTitle');
var IDBFS = 'IDBFS is no longer included by default; build with -lidbfs.js';
var PROXYFS = 'PROXYFS is no longer included by default; build with -lproxyfs.js';
var WORKERFS = 'WORKERFS is no longer included by default; build with -lworkerfs.js';
var NODEFS = 'NODEFS is no longer included by default; build with -lnodefs.js';

assert(
  ENVIRONMENT_IS_WEB || ENVIRONMENT_IS_WORKER || ENVIRONMENT_IS_NODE, 'Pthreads do not work in this environment yet (need Web Workers, or an alternative to them)');

assert(!ENVIRONMENT_IS_SHELL, "shell environment detected but not enabled at build time.  Add 'shell' to `-sENVIRONMENT` to enable.");


// end include: shell.js
// include: preamble.js
// === Preamble library stuff ===

// Documentation for the public APIs defined in this file must be updated in:
//    site/source/docs/api_reference/preamble.js.rst
// A prebuilt local version of the documentation is available at:
//    site/build/text/docs/api_reference/preamble.js.txt
// You can also build docs locally as HTML or other formats in site/
// An online HTML version (which may be of a different version of Emscripten)
//    is up at http://kripken.github.io/emscripten-site/docs/api_reference/preamble.js.html

var wasmBinary;
if (Module['wasmBinary']) wasmBinary = Module['wasmBinary'];legacyModuleProp('wasmBinary', 'wasmBinary');
var noExitRuntime = Module['noExitRuntime'] || true;legacyModuleProp('noExitRuntime', 'noExitRuntime');

if (typeof WebAssembly != 'object') {
  abort('no native wasm support detected');
}

// Wasm globals

var wasmMemory;

// For sending to workers.
var wasmModule;

//========================================
// Runtime essentials
//========================================

// whether we are quitting the application. no code should run after this.
// set in exit() and abort()
var ABORT = false;

// set by exit() and abort().  Passed to 'onExit' handler.
// NOTE: This is also used as the process return code code in shell environments
// but only when noExitRuntime is false.
var EXITSTATUS;

/** @type {function(*, string=)} */
function assert(condition, text) {
  if (!condition) {
    abort('Assertion failed' + (text ? ': ' + text : ''));
  }
}

// We used to include malloc/free by default in the past. Show a helpful error in
// builds with assertions.

// include: runtime_strings.js
// runtime_strings.js: String related runtime functions that are part of both
// MINIMAL_RUNTIME and regular runtime.

var UTF8Decoder = typeof TextDecoder != 'undefined' ? new TextDecoder('utf8') : undefined;

/**
 * Given a pointer 'idx' to a null-terminated UTF8-encoded string in the given
 * array that contains uint8 values, returns a copy of that string as a
 * Javascript String object.
 * heapOrArray is either a regular array, or a JavaScript typed array view.
 * @param {number} idx
 * @param {number=} maxBytesToRead
 * @return {string}
 */
function UTF8ArrayToString(heapOrArray, idx, maxBytesToRead) {
  var endIdx = idx + maxBytesToRead;
  var endPtr = idx;
  // TextDecoder needs to know the byte length in advance, it doesn't stop on
  // null terminator by itself.  Also, use the length info to avoid running tiny
  // strings through TextDecoder, since .subarray() allocates garbage.
  // (As a tiny code save trick, compare endPtr against endIdx using a negation,
  // so that undefined means Infinity)
  while (heapOrArray[endPtr] && !(endPtr >= endIdx)) ++endPtr;

  if (endPtr - idx > 16 && heapOrArray.buffer && UTF8Decoder) {
    return UTF8Decoder.decode(heapOrArray.buffer instanceof SharedArrayBuffer ? heapOrArray.slice(idx, endPtr) : heapOrArray.subarray(idx, endPtr));
  }
  var str = '';
  // If building with TextDecoder, we have already computed the string length
  // above, so test loop end condition against that
  while (idx < endPtr) {
    // For UTF8 byte structure, see:
    // http://en.wikipedia.org/wiki/UTF-8#Description
    // https://www.ietf.org/rfc/rfc2279.txt
    // https://tools.ietf.org/html/rfc3629
    var u0 = heapOrArray[idx++];
    if (!(u0 & 0x80)) { str += String.fromCharCode(u0); continue; }
    var u1 = heapOrArray[idx++] & 63;
    if ((u0 & 0xE0) == 0xC0) { str += String.fromCharCode(((u0 & 31) << 6) | u1); continue; }
    var u2 = heapOrArray[idx++] & 63;
    if ((u0 & 0xF0) == 0xE0) {
      u0 = ((u0 & 15) << 12) | (u1 << 6) | u2;
    } else {
      if ((u0 & 0xF8) != 0xF0) warnOnce('Invalid UTF-8 leading byte ' + ptrToString(u0) + ' encountered when deserializing a UTF-8 string in wasm memory to a JS string!');
      u0 = ((u0 & 7) << 18) | (u1 << 12) | (u2 << 6) | (heapOrArray[idx++] & 63);
    }

    if (u0 < 0x10000) {
      str += String.fromCharCode(u0);
    } else {
      var ch = u0 - 0x10000;
      str += String.fromCharCode(0xD800 | (ch >> 10), 0xDC00 | (ch & 0x3FF));
    }
  }
  return str;
}

/**
 * Given a pointer 'ptr' to a null-terminated UTF8-encoded string in the
 * emscripten HEAP, returns a copy of that string as a Javascript String object.
 *
 * @param {number} ptr
 * @param {number=} maxBytesToRead - An optional length that specifies the
 *   maximum number of bytes to read. You can omit this parameter to scan the
 *   string until the first \0 byte. If maxBytesToRead is passed, and the string
 *   at [ptr, ptr+maxBytesToReadr[ contains a null byte in the middle, then the
 *   string will cut short at that byte index (i.e. maxBytesToRead will not
 *   produce a string of exact length [ptr, ptr+maxBytesToRead[) N.B. mixing
 *   frequent uses of UTF8ToString() with and without maxBytesToRead may throw
 *   JS JIT optimizations off, so it is worth to consider consistently using one
 * @return {string}
 */
function UTF8ToString(ptr, maxBytesToRead) {
  assert(typeof ptr == 'number');
  return ptr ? UTF8ArrayToString(HEAPU8, ptr, maxBytesToRead) : '';
}

/**
 * Copies the given Javascript String object 'str' to the given byte array at
 * address 'outIdx', encoded in UTF8 form and null-terminated. The copy will
 * require at most str.length*4+1 bytes of space in the HEAP.  Use the function
 * lengthBytesUTF8 to compute the exact number of bytes (excluding null
 * terminator) that this function will write.
 *
 * @param {string} str - The Javascript string to copy.
 * @param {ArrayBufferView|Array<number>} heap - The array to copy to. Each
 *                                               index in this array is assumed
 *                                               to be one 8-byte element.
 * @param {number} outIdx - The starting offset in the array to begin the copying.
 * @param {number} maxBytesToWrite - The maximum number of bytes this function
 *                                   can write to the array.  This count should
 *                                   include the null terminator, i.e. if
 *                                   maxBytesToWrite=1, only the null terminator
 *                                   will be written and nothing else.
 *                                   maxBytesToWrite=0 does not write any bytes
 *                                   to the output, not even the null
 *                                   terminator.
 * @return {number} The number of bytes written, EXCLUDING the null terminator.
 */
function stringToUTF8Array(str, heap, outIdx, maxBytesToWrite) {
  // Parameter maxBytesToWrite is not optional. Negative values, 0, null,
  // undefined and false each don't write out any bytes.
  if (!(maxBytesToWrite > 0))
    return 0;

  var startIdx = outIdx;
  var endIdx = outIdx + maxBytesToWrite - 1; // -1 for string null terminator.
  for (var i = 0; i < str.length; ++i) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code
    // unit, not a Unicode code point of the character! So decode
    // UTF16->UTF32->UTF8.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    // For UTF8 byte structure, see http://en.wikipedia.org/wiki/UTF-8#Description
    // and https://www.ietf.org/rfc/rfc2279.txt
    // and https://tools.ietf.org/html/rfc3629
    var u = str.charCodeAt(i); // possibly a lead surrogate
    if (u >= 0xD800 && u <= 0xDFFF) {
      var u1 = str.charCodeAt(++i);
      u = 0x10000 + ((u & 0x3FF) << 10) | (u1 & 0x3FF);
    }
    if (u <= 0x7F) {
      if (outIdx >= endIdx) break;
      heap[outIdx++] = u;
    } else if (u <= 0x7FF) {
      if (outIdx + 1 >= endIdx) break;
      heap[outIdx++] = 0xC0 | (u >> 6);
      heap[outIdx++] = 0x80 | (u & 63);
    } else if (u <= 0xFFFF) {
      if (outIdx + 2 >= endIdx) break;
      heap[outIdx++] = 0xE0 | (u >> 12);
      heap[outIdx++] = 0x80 | ((u >> 6) & 63);
      heap[outIdx++] = 0x80 | (u & 63);
    } else {
      if (outIdx + 3 >= endIdx) break;
      if (u > 0x10FFFF) warnOnce('Invalid Unicode code point ' + ptrToString(u) + ' encountered when serializing a JS string to a UTF-8 string in wasm memory! (Valid unicode code points should be in range 0-0x10FFFF).');
      heap[outIdx++] = 0xF0 | (u >> 18);
      heap[outIdx++] = 0x80 | ((u >> 12) & 63);
      heap[outIdx++] = 0x80 | ((u >> 6) & 63);
      heap[outIdx++] = 0x80 | (u & 63);
    }
  }
  // Null-terminate the pointer to the buffer.
  heap[outIdx] = 0;
  return outIdx - startIdx;
}

/**
 * Copies the given Javascript String object 'str' to the emscripten HEAP at
 * address 'outPtr', null-terminated and encoded in UTF8 form. The copy will
 * require at most str.length*4+1 bytes of space in the HEAP.
 * Use the function lengthBytesUTF8 to compute the exact number of bytes
 * (excluding null terminator) that this function will write.
 *
 * @return {number} The number of bytes written, EXCLUDING the null terminator.
 */
function stringToUTF8(str, outPtr, maxBytesToWrite) {
  assert(typeof maxBytesToWrite == 'number', 'stringToUTF8(str, outPtr, maxBytesToWrite) is missing the third parameter that specifies the length of the output buffer!');
  return stringToUTF8Array(str, HEAPU8,outPtr, maxBytesToWrite);
}

/**
 * Returns the number of bytes the given Javascript string takes if encoded as a
 * UTF8 byte array, EXCLUDING the null terminator byte.
 *
 * @param {string} str - JavaScript string to operator on
 * @return {number} Length, in bytes, of the UTF8 encoded string.
 */
function lengthBytesUTF8(str) {
  var len = 0;
  for (var i = 0; i < str.length; ++i) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code
    // unit, not a Unicode code point of the character! So decode
    // UTF16->UTF32->UTF8.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    var c = str.charCodeAt(i); // possibly a lead surrogate
    if (c <= 0x7F) {
      len++;
    } else if (c <= 0x7FF) {
      len += 2;
    } else if (c >= 0xD800 && c <= 0xDFFF) {
      len += 4; ++i;
    } else {
      len += 3;
    }
  }
  return len;
}

// end include: runtime_strings.js
// Memory management

var HEAP,
/** @type {!Int8Array} */
  HEAP8,
/** @type {!Uint8Array} */
  HEAPU8,
/** @type {!Int16Array} */
  HEAP16,
/** @type {!Uint16Array} */
  HEAPU16,
/** @type {!Int32Array} */
  HEAP32,
/** @type {!Uint32Array} */
  HEAPU32,
/** @type {!Float32Array} */
  HEAPF32,
/* BigInt64Array type is not correctly defined in closure
/** not-@type {!BigInt64Array} */
  HEAP64,
/* BigUInt64Array type is not correctly defined in closure
/** not-t@type {!BigUint64Array} */
  HEAPU64,
/** @type {!Float64Array} */
  HEAPF64;

function updateMemoryViews() {
  var b = wasmMemory.buffer;
  Module['HEAP8'] = HEAP8 = new Int8Array(b);
  Module['HEAP16'] = HEAP16 = new Int16Array(b);
  Module['HEAP32'] = HEAP32 = new Int32Array(b);
  Module['HEAPU8'] = HEAPU8 = new Uint8Array(b);
  Module['HEAPU16'] = HEAPU16 = new Uint16Array(b);
  Module['HEAPU32'] = HEAPU32 = new Uint32Array(b);
  Module['HEAPF32'] = HEAPF32 = new Float32Array(b);
  Module['HEAPF64'] = HEAPF64 = new Float64Array(b);
  Module['HEAP64'] = HEAP64 = new BigInt64Array(b);
  Module['HEAPU64'] = HEAPU64 = new BigUint64Array(b);
}

assert(!Module['STACK_SIZE'], 'STACK_SIZE can no longer be set at runtime.  Use -sSTACK_SIZE at link time')

assert(typeof Int32Array != 'undefined' && typeof Float64Array !== 'undefined' && Int32Array.prototype.subarray != undefined && Int32Array.prototype.set != undefined,
       'JS engine does not provide full typed array support');

// In non-standalone/normal mode, we create the memory here.
// include: runtime_init_memory.js
// Create the wasm memory. (Note: this only applies if IMPORTED_MEMORY is defined)

var INITIAL_MEMORY = Module['INITIAL_MEMORY'] || 1073741824;legacyModuleProp('INITIAL_MEMORY', 'INITIAL_MEMORY');

assert(INITIAL_MEMORY >= 65536, 'INITIAL_MEMORY should be larger than STACK_SIZE, was ' + INITIAL_MEMORY + '! (STACK_SIZE=' + 65536 + ')');

// check for full engine support (use string 'subarray' to avoid closure compiler confusion)

if (ENVIRONMENT_IS_PTHREAD) {
  wasmMemory = Module['wasmMemory'];
} else {

  if (Module['wasmMemory']) {
    wasmMemory = Module['wasmMemory'];
  } else
  {
    wasmMemory = new WebAssembly.Memory({
      'initial': INITIAL_MEMORY / 65536,
      'maximum': INITIAL_MEMORY / 65536
      ,
      'shared': true
    });
    if (!(wasmMemory.buffer instanceof SharedArrayBuffer)) {
      err('requested a shared WebAssembly.Memory but the returned buffer is not a SharedArrayBuffer, indicating that while the browser has SharedArrayBuffer it does not have WebAssembly threads support - you may need to set a flag');
      if (ENVIRONMENT_IS_NODE) {
        err('(on node you may need: --experimental-wasm-threads --experimental-wasm-bulk-memory and/or recent version)');
      }
      throw Error('bad memory');
    }
  }

}

updateMemoryViews();

// If the user provides an incorrect length, just use that length instead rather than providing the user to
// specifically provide the memory length with Module['INITIAL_MEMORY'].
INITIAL_MEMORY = wasmMemory.buffer.byteLength;
assert(INITIAL_MEMORY % 65536 === 0);

// end include: runtime_init_memory.js

// include: runtime_init_table.js
// In regular non-RELOCATABLE mode the table is exported
// from the wasm module and this will be assigned once
// the exports are available.
var wasmTable;

// end include: runtime_init_table.js
// include: runtime_stack_check.js
// Initializes the stack cookie. Called at the startup of main and at the startup of each thread in pthreads mode.
function writeStackCookie() {
  var max = _emscripten_stack_get_end();
  assert((max & 3) == 0);
  // If the stack ends at address zero we write our cookies 4 bytes into the
  // stack.  This prevents interference with the (separate) address-zero check
  // below.
  if (max == 0) {
    max += 4;
  }
  // The stack grow downwards towards _emscripten_stack_get_end.
  // We write cookies to the final two words in the stack and detect if they are
  // ever overwritten.
  HEAPU32[((max)>>2)] = 0x02135467;
  HEAPU32[(((max)+(4))>>2)] = 0x89BACDFE;
  // Also test the global address 0 for integrity.
  HEAPU32[0] = 0x63736d65; /* 'emsc' */
}

function checkStackCookie() {
  if (ABORT) return;
  var max = _emscripten_stack_get_end();
  // See writeStackCookie().
  if (max == 0) {
    max += 4;
  }
  var cookie1 = HEAPU32[((max)>>2)];
  var cookie2 = HEAPU32[(((max)+(4))>>2)];
  if (cookie1 != 0x02135467 || cookie2 != 0x89BACDFE) {
    abort('Stack overflow! Stack cookie has been overwritten at ' + ptrToString(max) + ', expected hex dwords 0x89BACDFE and 0x2135467, but received ' + ptrToString(cookie2) + ' ' + ptrToString(cookie1));
  }
  // Also test the global address 0 for integrity.
  if (HEAPU32[0] !== 0x63736d65 /* 'emsc' */) {
    abort('Runtime error: The application has corrupted its heap memory area (address zero)!');
  }
}

// end include: runtime_stack_check.js
// include: runtime_assertions.js
// Endianness check
(function() {
  var h16 = new Int16Array(1);
  var h8 = new Int8Array(h16.buffer);
  h16[0] = 0x6373;
  if (h8[0] !== 0x73 || h8[1] !== 0x63) throw 'Runtime error: expected the system to be little-endian! (Run with -sSUPPORT_BIG_ENDIAN to bypass)';
})();

// end include: runtime_assertions.js
var __ATPRERUN__  = []; // functions called before the runtime is initialized
var __ATINIT__    = []; // functions called during startup
var __ATEXIT__    = []; // functions called during shutdown
var __ATPOSTRUN__ = []; // functions called after the main() is called

var runtimeInitialized = false;

function keepRuntimeAlive() {
  return noExitRuntime;
}

function preRun() {
  assert(!ENVIRONMENT_IS_PTHREAD); // PThreads reuse the runtime from the main thread.
  if (Module['preRun']) {
    if (typeof Module['preRun'] == 'function') Module['preRun'] = [Module['preRun']];
    while (Module['preRun'].length) {
      addOnPreRun(Module['preRun'].shift());
    }
  }
  callRuntimeCallbacks(__ATPRERUN__);
}

function initRuntime() {
  assert(!runtimeInitialized);
  runtimeInitialized = true;

  if (ENVIRONMENT_IS_PTHREAD) return;

  checkStackCookie();

  
if (!Module["noFSInit"] && !FS.init.initialized)
  FS.init();
FS.ignorePermissions = false;

TTY.init();
  callRuntimeCallbacks(__ATINIT__);
}

function postRun() {
  checkStackCookie();
  if (ENVIRONMENT_IS_PTHREAD) return; // PThreads reuse the runtime from the main thread.

  if (Module['postRun']) {
    if (typeof Module['postRun'] == 'function') Module['postRun'] = [Module['postRun']];
    while (Module['postRun'].length) {
      addOnPostRun(Module['postRun'].shift());
    }
  }

  callRuntimeCallbacks(__ATPOSTRUN__);
}

function addOnPreRun(cb) {
  __ATPRERUN__.unshift(cb);
}

function addOnInit(cb) {
  __ATINIT__.unshift(cb);
}

function addOnExit(cb) {
}

function addOnPostRun(cb) {
  __ATPOSTRUN__.unshift(cb);
}

// include: runtime_math.js
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Math/imul

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Math/fround

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Math/clz32

// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Math/trunc

assert(Math.imul, 'This browser does not support Math.imul(), build with LEGACY_VM_SUPPORT or POLYFILL_OLD_MATH_FUNCTIONS to add in a polyfill');
assert(Math.fround, 'This browser does not support Math.fround(), build with LEGACY_VM_SUPPORT or POLYFILL_OLD_MATH_FUNCTIONS to add in a polyfill');
assert(Math.clz32, 'This browser does not support Math.clz32(), build with LEGACY_VM_SUPPORT or POLYFILL_OLD_MATH_FUNCTIONS to add in a polyfill');
assert(Math.trunc, 'This browser does not support Math.trunc(), build with LEGACY_VM_SUPPORT or POLYFILL_OLD_MATH_FUNCTIONS to add in a polyfill');

// end include: runtime_math.js
// A counter of dependencies for calling run(). If we need to
// do asynchronous work before running, increment this and
// decrement it. Incrementing must happen in a place like
// Module.preRun (used by emcc to add file preloading).
// Note that you can add dependencies in preRun, even though
// it happens right before run - run will be postponed until
// the dependencies are met.
var runDependencies = 0;
var runDependencyWatcher = null;
var dependenciesFulfilled = null; // overridden to take different actions when all run dependencies are fulfilled
var runDependencyTracking = {};

function getUniqueRunDependency(id) {
  var orig = id;
  while (1) {
    if (!runDependencyTracking[id]) return id;
    id = orig + Math.random();
  }
}

function addRunDependency(id) {
  runDependencies++;

  if (Module['monitorRunDependencies']) {
    Module['monitorRunDependencies'](runDependencies);
  }

  if (id) {
    assert(!runDependencyTracking[id]);
    runDependencyTracking[id] = 1;
    if (runDependencyWatcher === null && typeof setInterval != 'undefined') {
      // Check for missing dependencies every few seconds
      runDependencyWatcher = setInterval(function() {
        if (ABORT) {
          clearInterval(runDependencyWatcher);
          runDependencyWatcher = null;
          return;
        }
        var shown = false;
        for (var dep in runDependencyTracking) {
          if (!shown) {
            shown = true;
            err('still waiting on run dependencies:');
          }
          err('dependency: ' + dep);
        }
        if (shown) {
          err('(end of list)');
        }
      }, 10000);
    }
  } else {
    err('warning: run dependency added without ID');
  }
}

function removeRunDependency(id) {
  runDependencies--;

  if (Module['monitorRunDependencies']) {
    Module['monitorRunDependencies'](runDependencies);
  }

  if (id) {
    assert(runDependencyTracking[id]);
    delete runDependencyTracking[id];
  } else {
    err('warning: run dependency removed without ID');
  }
  if (runDependencies == 0) {
    if (runDependencyWatcher !== null) {
      clearInterval(runDependencyWatcher);
      runDependencyWatcher = null;
    }
    if (dependenciesFulfilled) {
      var callback = dependenciesFulfilled;
      dependenciesFulfilled = null;
      callback(); // can add another dependenciesFulfilled
    }
  }
}

/** @param {string|number=} what */
function abort(what) {
  if (Module['onAbort']) {
    Module['onAbort'](what);
  }

  what = 'Aborted(' + what + ')';
  // TODO(sbc): Should we remove printing and leave it up to whoever
  // catches the exception?
  err(what);

  ABORT = true;
  EXITSTATUS = 1;

  // Use a wasm runtime error, because a JS error might be seen as a foreign
  // exception, which means we'd run destructors on it. We need the error to
  // simply make the program stop.
  // FIXME This approach does not work in Wasm EH because it currently does not assume
  // all RuntimeErrors are from traps; it decides whether a RuntimeError is from
  // a trap or not based on a hidden field within the object. So at the moment
  // we don't have a way of throwing a wasm trap from JS. TODO Make a JS API that
  // allows this in the wasm spec.

  // Suppress closure compiler warning here. Closure compiler's builtin extern
  // defintion for WebAssembly.RuntimeError claims it takes no arguments even
  // though it can.
  // TODO(https://github.com/google/closure-compiler/pull/3913): Remove if/when upstream closure gets fixed.
  /** @suppress {checkTypes} */
  var e = new WebAssembly.RuntimeError(what);

  readyPromiseReject(e);
  // Throw the error whether or not MODULARIZE is set because abort is used
  // in code paths apart from instantiation where an exception is expected
  // to be thrown when abort is called.
  throw e;
}

// include: memoryprofiler.js
// end include: memoryprofiler.js
// include: URIUtils.js
// Prefix of data URIs emitted by SINGLE_FILE and related options.
var dataURIPrefix = 'data:application/octet-stream;base64,';

// Indicates whether filename is a base64 data URI.
function isDataURI(filename) {
  // Prefix of data URIs emitted by SINGLE_FILE and related options.
  return filename.startsWith(dataURIPrefix);
}

// Indicates whether filename is delivered via file protocol (as opposed to http/https)
function isFileURI(filename) {
  return filename.startsWith('file://');
}

// end include: URIUtils.js
/** @param {boolean=} fixedasm */
function createExportWrapper(name, fixedasm) {
  return function() {
    var displayName = name;
    var asm = fixedasm;
    if (!fixedasm) {
      asm = Module['asm'];
    }
    assert(runtimeInitialized, 'native function `' + displayName + '` called before runtime initialization');
    if (!asm[name]) {
      assert(asm[name], 'exported native function `' + displayName + '` not found');
    }
    return asm[name].apply(null, arguments);
  };
}

// include: runtime_exceptions.js
// Base Emscripten EH error class
class EmscriptenEH extends Error {}

class EmscriptenSjLj extends EmscriptenEH {}

class CppException extends EmscriptenEH {
  constructor(excPtr) {
    super(excPtr);
    const excInfo = getExceptionMessage(excPtr);
    this.name = excInfo[0];
    this.message = excInfo[1];
  }
}

// end include: runtime_exceptions.js
var wasmBinaryFile;
  wasmBinaryFile = 'z3-built.wasm';
  if (!isDataURI(wasmBinaryFile)) {
    wasmBinaryFile = locateFile(wasmBinaryFile);
  }

function getBinary(file) {
  try {
    if (file == wasmBinaryFile && wasmBinary) {
      return new Uint8Array(wasmBinary);
    }
    if (readBinary) {
      return readBinary(file);
    }
    throw "both async and sync fetching of the wasm failed";
  }
  catch (err) {
    abort(err);
  }
}

function getBinaryPromise(binaryFile) {
  // If we don't have the binary yet, try to to load it asynchronously.
  // Fetch has some additional restrictions over XHR, like it can't be used on a file:// url.
  // See https://github.com/github/fetch/pull/92#issuecomment-140665932
  // Cordova or Electron apps are typically loaded from a file:// url.
  // So use fetch if it is available and the url is not a file, otherwise fall back to XHR.
  if (!wasmBinary && (ENVIRONMENT_IS_WEB || ENVIRONMENT_IS_WORKER)) {
    if (typeof fetch == 'function'
      && !isFileURI(binaryFile)
    ) {
      return fetch(binaryFile, { credentials: 'same-origin' }).then(function(response) {
        if (!response['ok']) {
          throw "failed to load wasm binary file at '" + binaryFile + "'";
        }
        return response['arrayBuffer']();
      }).catch(function () {
          return getBinary(binaryFile);
      });
    }
    else {
      if (readAsync) {
        // fetch is not available or url is file => try XHR (readAsync uses XHR internally)
        return new Promise(function(resolve, reject) {
          readAsync(binaryFile, function(response) { resolve(new Uint8Array(/** @type{!ArrayBuffer} */(response))) }, reject)
        });
      }
    }
  }

  // Otherwise, getBinary should be able to get it synchronously
  return Promise.resolve().then(function() { return getBinary(binaryFile); });
}

function instantiateArrayBuffer(binaryFile, imports, receiver) {
  return getBinaryPromise(binaryFile).then(function(binary) {
    return WebAssembly.instantiate(binary, imports);
  }).then(function (instance) {
    return instance;
  }).then(receiver, function(reason) {
    err('failed to asynchronously prepare wasm: ' + reason);

    // Warn on some common problems.
    if (isFileURI(wasmBinaryFile)) {
      err('warning: Loading from a file URI (' + wasmBinaryFile + ') is not supported in most browsers. See https://emscripten.org/docs/getting_started/FAQ.html#how-do-i-run-a-local-webserver-for-testing-why-does-my-program-stall-in-downloading-or-preparing');
    }
    abort(reason);
  });
}

function instantiateAsync(binary, binaryFile, imports, callback) {
  if (!binary &&
      typeof WebAssembly.instantiateStreaming == 'function' &&
      !isDataURI(binaryFile) &&
      // Don't use streaming for file:// delivered objects in a webview, fetch them synchronously.
      !isFileURI(binaryFile) &&
      // Avoid instantiateStreaming() on Node.js environment for now, as while
      // Node.js v18.1.0 implements it, it does not have a full fetch()
      // implementation yet.
      //
      // Reference:
      //   https://github.com/emscripten-core/emscripten/pull/16917
      !ENVIRONMENT_IS_NODE &&
      typeof fetch == 'function') {
    return fetch(binaryFile, { credentials: 'same-origin' }).then(function(response) {
      // Suppress closure warning here since the upstream definition for
      // instantiateStreaming only allows Promise<Repsponse> rather than
      // an actual Response.
      // TODO(https://github.com/google/closure-compiler/pull/3913): Remove if/when upstream closure is fixed.
      /** @suppress {checkTypes} */
      var result = WebAssembly.instantiateStreaming(response, imports);

      return result.then(
        callback,
        function(reason) {
          // We expect the most common failure cause to be a bad MIME type for the binary,
          // in which case falling back to ArrayBuffer instantiation should work.
          err('wasm streaming compile failed: ' + reason);
          err('falling back to ArrayBuffer instantiation');
          return instantiateArrayBuffer(binaryFile, imports, callback);
        });
    });
  } else {
    return instantiateArrayBuffer(binaryFile, imports, callback);
  }
}

// Create the wasm instance.
// Receives the wasm imports, returns the exports.
function createWasm() {
  // prepare imports
  var info = {
    'env': wasmImports,
    'wasi_snapshot_preview1': wasmImports,
  };
  // Load the wasm module and create an instance of using native support in the JS engine.
  // handle a generated wasm instance, receiving its exports and
  // performing other necessary setup
  /** @param {WebAssembly.Module=} module*/
  function receiveInstance(instance, module) {
    var exports = instance.exports;

    Module['asm'] = exports;

    registerTLSInit(Module['asm']['_emscripten_tls_init']);

    wasmTable = Module['asm']['__indirect_function_table'];
    assert(wasmTable, "table not found in wasm exports");

    addOnInit(Module['asm']['__wasm_call_ctors']);

    // We now have the Wasm module loaded up, keep a reference to the compiled module so we can post it to the workers.
    wasmModule = module;

    PThread.loadWasmModuleToAllWorkers(() => removeRunDependency('wasm-instantiate'));

    return exports;
  }
  // wait for the pthread pool (if any)
  addRunDependency('wasm-instantiate');

  // Prefer streaming instantiation if available.
  // Async compilation can be confusing when an error on the page overwrites Module
  // (for example, if the order of elements is wrong, and the one defining Module is
  // later), so we save Module and check it later.
  var trueModule = Module;
  function receiveInstantiationResult(result) {
    // 'result' is a ResultObject object which has both the module and instance.
    // receiveInstance() will swap in the exports (to Module.asm) so they can be called
    assert(Module === trueModule, 'the Module object should not be replaced during async compilation - perhaps the order of HTML elements is wrong?');
    trueModule = null;
    receiveInstance(result['instance'], result['module']);
  }

  // User shell pages can write their own Module.instantiateWasm = function(imports, successCallback) callback
  // to manually instantiate the Wasm module themselves. This allows pages to run the instantiation parallel
  // to any other async startup actions they are performing.
  // Also pthreads and wasm workers initialize the wasm instance through this path.
  if (Module['instantiateWasm']) {
    try {
      return Module['instantiateWasm'](info, receiveInstance);
    } catch(e) {
      err('Module.instantiateWasm callback failed with error: ' + e);
        // If instantiation fails, reject the module ready promise.
        readyPromiseReject(e);
    }
  }

  // If instantiation fails, reject the module ready promise.
  instantiateAsync(wasmBinary, wasmBinaryFile, info, receiveInstantiationResult).catch(readyPromiseReject);
  return {}; // no exports yet; we'll fill them in later
}

// Globals used by JS i64 conversions (see makeSetValue)
var tempDouble;
var tempI64;

// include: runtime_debug.js
function legacyModuleProp(prop, newName) {
  if (!Object.getOwnPropertyDescriptor(Module, prop)) {
    Object.defineProperty(Module, prop, {
      configurable: true,
      get: function() {
        abort('Module.' + prop + ' has been replaced with plain ' + newName + ' (the initial value can be provided on Module, but after startup the value is only looked for on a local variable of that name)');
      }
    });
  }
}

function ignoredModuleProp(prop) {
  if (Object.getOwnPropertyDescriptor(Module, prop)) {
    abort('`Module.' + prop + '` was supplied but `' + prop + '` not included in INCOMING_MODULE_JS_API');
  }
}

// forcing the filesystem exports a few things by default
function isExportedByForceFilesystem(name) {
  return name === 'FS_createPath' ||
         name === 'FS_createDataFile' ||
         name === 'FS_createPreloadedFile' ||
         name === 'FS_unlink' ||
         name === 'addRunDependency' ||
         // The old FS has some functionality that WasmFS lacks.
         name === 'FS_createLazyFile' ||
         name === 'FS_createDevice' ||
         name === 'removeRunDependency';
}

function missingGlobal(sym, msg) {
  if (typeof globalThis !== 'undefined') {
    Object.defineProperty(globalThis, sym, {
      configurable: true,
      get: function() {
        warnOnce('`' + sym + '` is not longer defined by emscripten. ' + msg);
        return undefined;
      }
    });
  }
}

missingGlobal('buffer', 'Please use HEAP8.buffer or wasmMemory.buffer');

function missingLibrarySymbol(sym) {
  if (typeof globalThis !== 'undefined' && !Object.getOwnPropertyDescriptor(globalThis, sym)) {
    Object.defineProperty(globalThis, sym, {
      configurable: true,
      get: function() {
        // Can't `abort()` here because it would break code that does runtime
        // checks.  e.g. `if (typeof SDL === 'undefined')`.
        var msg = '`' + sym + '` is a library symbol and not included by default; add it to your library.js __deps or to DEFAULT_LIBRARY_FUNCS_TO_INCLUDE on the command line';
        // DEFAULT_LIBRARY_FUNCS_TO_INCLUDE requires the name as it appears in
        // library.js, which means $name for a JS name with no prefix, or name
        // for a JS name like _name.
        var librarySymbol = sym;
        if (!librarySymbol.startsWith('_')) {
          librarySymbol = '$' + sym;
        }
        msg += " (e.g. -sDEFAULT_LIBRARY_FUNCS_TO_INCLUDE=" + librarySymbol + ")";
        if (isExportedByForceFilesystem(sym)) {
          msg += '. Alternatively, forcing filesystem support (-sFORCE_FILESYSTEM) can export this for you';
        }
        warnOnce(msg);
        return undefined;
      }
    });
  }
  // Any symbol that is not included from the JS libary is also (by definition)
  // not exported on the Module object.
  unexportedRuntimeSymbol(sym);
}

function unexportedRuntimeSymbol(sym) {
  if (!Object.getOwnPropertyDescriptor(Module, sym)) {
    Object.defineProperty(Module, sym, {
      configurable: true,
      get: function() {
        var msg = "'" + sym + "' was not exported. add it to EXPORTED_RUNTIME_METHODS (see the FAQ)";
        if (isExportedByForceFilesystem(sym)) {
          msg += '. Alternatively, forcing filesystem support (-sFORCE_FILESYSTEM) can export this for you';
        }
        abort(msg);
      }
    });
  }
}

// Used by XXXXX_DEBUG settings to output debug messages.
function dbg(text) {
  // Avoid using the console for debugging in multi-threaded node applications
  // See https://github.com/emscripten-core/emscripten/issues/14804
  if (ENVIRONMENT_IS_NODE) {
    fs.writeSync(2, text + '\n');
  } else
  // TODO(sbc): Make this configurable somehow.  Its not always convenient for
  // logging to show up as errors.
  console.error(text);
}

// end include: runtime_debug.js
// === Body ===

var ASM_CONSTS = {
  499620: ($0) => { resolve_async(UTF8ToString($0)); },  
 499657: () => { reject_async(new Error('failed with unknown exception')); },  
 499719: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 499766: ($0) => { resolve_async($0); },  
 499789: () => { reject_async('failed with unknown exception'); },  
 499840: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 499887: ($0) => { resolve_async($0); },  
 499910: () => { reject_async('failed with unknown exception'); },  
 499961: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500008: ($0) => { resolve_async($0); },  
 500031: () => { reject_async('failed with unknown exception'); },  
 500082: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500129: ($0) => { resolve_async($0); },  
 500152: () => { reject_async('failed with unknown exception'); },  
 500203: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500250: ($0) => { resolve_async($0); },  
 500273: () => { reject_async('failed with unknown exception'); },  
 500324: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500371: ($0) => { resolve_async($0); },  
 500394: () => { reject_async('failed with unknown exception'); },  
 500445: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500492: ($0) => { resolve_async($0); },  
 500515: () => { reject_async('failed with unknown exception'); },  
 500566: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500613: ($0) => { resolve_async($0); },  
 500636: () => { reject_async('failed with unknown exception'); },  
 500687: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500734: ($0) => { resolve_async($0); },  
 500757: () => { reject_async('failed with unknown exception'); },  
 500808: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500855: ($0) => { resolve_async($0); },  
 500878: () => { reject_async('failed with unknown exception'); },  
 500929: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 500976: ($0) => { resolve_async($0); },  
 500999: () => { reject_async('failed with unknown exception'); },  
 501050: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 501097: ($0) => { resolve_async($0); },  
 501120: () => { reject_async('failed with unknown exception'); },  
 501171: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 501218: ($0) => { resolve_async($0); },  
 501241: () => { reject_async('failed with unknown exception'); },  
 501292: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 501339: ($0) => { resolve_async($0); },  
 501362: () => { reject_async('failed with unknown exception'); },  
 501413: ($0) => { reject_async(new Error(UTF8ToString($0))); },  
 501460: ($0) => { resolve_async($0); },  
 501483: () => { reject_async('failed with unknown exception'); },  
 501534: ($0) => { reject_async(new Error(UTF8ToString($0))); }
};



// end include: preamble.js

  /** @constructor */
  function ExitStatus(status) {
      this.name = 'ExitStatus';
      this.message = 'Program terminated with exit(' + status + ')';
      this.status = status;
    }

  
  
  function terminateWorker(worker) {
      worker.terminate();
      // terminate() can be asynchronous, so in theory the worker can continue
      // to run for some amount of time after termination.  However from our POV
      // the worker now dead and we don't want to hear from it again, so we stub
      // out its message handler here.  This avoids having to check in each of
      // the onmessage handlers if the message was coming from valid worker.
      worker.onmessage = (e) => {
        var cmd = e['data']['cmd'];
        err('received "' + cmd + '" command from terminated worker: ' + worker.workerID);
      };
    }
  
  function killThread(pthread_ptr) {
      assert(!ENVIRONMENT_IS_PTHREAD, 'Internal Error! killThread() can only ever be called from main application thread!');
      assert(pthread_ptr, 'Internal Error! Null pthread_ptr in killThread!');
      var worker = PThread.pthreads[pthread_ptr];
      delete PThread.pthreads[pthread_ptr];
      terminateWorker(worker);
      __emscripten_thread_free_data(pthread_ptr);
      // The worker was completely nuked (not just the pthread execution it was hosting), so remove it from running workers
      // but don't put it back to the pool.
      PThread.runningWorkers.splice(PThread.runningWorkers.indexOf(worker), 1); // Not a running Worker anymore.
      worker.pthread_ptr = 0;
    }
  
  function cancelThread(pthread_ptr) {
      assert(!ENVIRONMENT_IS_PTHREAD, 'Internal Error! cancelThread() can only ever be called from main application thread!');
      assert(pthread_ptr, 'Internal Error! Null pthread_ptr in cancelThread!');
      var worker = PThread.pthreads[pthread_ptr];
      worker.postMessage({ 'cmd': 'cancel' });
    }
  
  function cleanupThread(pthread_ptr) {
      assert(!ENVIRONMENT_IS_PTHREAD, 'Internal Error! cleanupThread() can only ever be called from main application thread!');
      assert(pthread_ptr, 'Internal Error! Null pthread_ptr in cleanupThread!');
      var worker = PThread.pthreads[pthread_ptr];
      assert(worker);
      PThread.returnWorkerToPool(worker);
    }
  
  function zeroMemory(address, size) {
      HEAPU8.fill(0, address, address + size);
      return address;
    }
  
  function spawnThread(threadParams) {
      assert(!ENVIRONMENT_IS_PTHREAD, 'Internal Error! spawnThread() can only ever be called from main application thread!');
      assert(threadParams.pthread_ptr, 'Internal error, no pthread ptr!');
  
      var worker = PThread.getNewWorker();
      if (!worker) {
        // No available workers in the PThread pool.
        return 6;
      }
      assert(!worker.pthread_ptr, 'Internal error!');
  
      PThread.runningWorkers.push(worker);
  
      // Add to pthreads map
      PThread.pthreads[threadParams.pthread_ptr] = worker;
  
      worker.pthread_ptr = threadParams.pthread_ptr;
      var msg = {
          'cmd': 'run',
          'start_routine': threadParams.startRoutine,
          'arg': threadParams.arg,
          'pthread_ptr': threadParams.pthread_ptr,
      };
      // Ask the worker to start executing its pthread entry point function.
      if (ENVIRONMENT_IS_NODE) {
        // Mark worker as strongly referenced once we start executing a pthread,
        // so that Node.js doesn't exit while the pthread is running.
        worker.ref();
      }
      worker.postMessage(msg, threadParams.transferList);
      return 0;
    }
  
  
  
  var PATH = {isAbs:(path) => path.charAt(0) === '/',splitPath:(filename) => {
        var splitPathRe = /^(\/?|)([\s\S]*?)((?:\.{1,2}|[^\/]+?|)(\.[^.\/]*|))(?:[\/]*)$/;
        return splitPathRe.exec(filename).slice(1);
      },normalizeArray:(parts, allowAboveRoot) => {
        // if the path tries to go above the root, `up` ends up > 0
        var up = 0;
        for (var i = parts.length - 1; i >= 0; i--) {
          var last = parts[i];
          if (last === '.') {
            parts.splice(i, 1);
          } else if (last === '..') {
            parts.splice(i, 1);
            up++;
          } else if (up) {
            parts.splice(i, 1);
            up--;
          }
        }
        // if the path is allowed to go above the root, restore leading ..s
        if (allowAboveRoot) {
          for (; up; up--) {
            parts.unshift('..');
          }
        }
        return parts;
      },normalize:(path) => {
        var isAbsolute = PATH.isAbs(path),
            trailingSlash = path.substr(-1) === '/';
        // Normalize the path
        path = PATH.normalizeArray(path.split('/').filter((p) => !!p), !isAbsolute).join('/');
        if (!path && !isAbsolute) {
          path = '.';
        }
        if (path && trailingSlash) {
          path += '/';
        }
        return (isAbsolute ? '/' : '') + path;
      },dirname:(path) => {
        var result = PATH.splitPath(path),
            root = result[0],
            dir = result[1];
        if (!root && !dir) {
          // No dirname whatsoever
          return '.';
        }
        if (dir) {
          // It has a dirname, strip trailing slash
          dir = dir.substr(0, dir.length - 1);
        }
        return root + dir;
      },basename:(path) => {
        // EMSCRIPTEN return '/'' for '/', not an empty string
        if (path === '/') return '/';
        path = PATH.normalize(path);
        path = path.replace(/\/$/, "");
        var lastSlash = path.lastIndexOf('/');
        if (lastSlash === -1) return path;
        return path.substr(lastSlash+1);
      },join:function() {
        var paths = Array.prototype.slice.call(arguments);
        return PATH.normalize(paths.join('/'));
      },join2:(l, r) => {
        return PATH.normalize(l + '/' + r);
      }};
  
  function getRandomDevice() {
      if (typeof crypto == 'object' && typeof crypto['getRandomValues'] == 'function') {
        // for modern web browsers
        var randomBuffer = new Uint8Array(1);
        return () => { crypto.getRandomValues(randomBuffer); return randomBuffer[0]; };
      } else
      if (ENVIRONMENT_IS_NODE) {
        // for nodejs with or without crypto support included
        try {
          var crypto_module = require('crypto');
          // nodejs has crypto support
          return () => crypto_module['randomBytes'](1)[0];
        } catch (e) {
          // nodejs doesn't have crypto support
        }
      }
      // we couldn't find a proper implementation, as Math.random() is not suitable for /dev/random, see emscripten-core/emscripten/pull/7096
      return () => abort("no cryptographic support found for randomDevice. consider polyfilling it if you want to use something insecure like Math.random(), e.g. put this in a --pre-js: var crypto = { getRandomValues: function(array) { for (var i = 0; i < array.length; i++) array[i] = (Math.random()*256)|0 } };");
    }
  
  
  
  var PATH_FS = {resolve:function() {
        var resolvedPath = '',
          resolvedAbsolute = false;
        for (var i = arguments.length - 1; i >= -1 && !resolvedAbsolute; i--) {
          var path = (i >= 0) ? arguments[i] : FS.cwd();
          // Skip empty and invalid entries
          if (typeof path != 'string') {
            throw new TypeError('Arguments to path.resolve must be strings');
          } else if (!path) {
            return ''; // an invalid portion invalidates the whole thing
          }
          resolvedPath = path + '/' + resolvedPath;
          resolvedAbsolute = PATH.isAbs(path);
        }
        // At this point the path should be resolved to a full absolute path, but
        // handle relative paths to be safe (might happen when process.cwd() fails)
        resolvedPath = PATH.normalizeArray(resolvedPath.split('/').filter((p) => !!p), !resolvedAbsolute).join('/');
        return ((resolvedAbsolute ? '/' : '') + resolvedPath) || '.';
      },relative:(from, to) => {
        from = PATH_FS.resolve(from).substr(1);
        to = PATH_FS.resolve(to).substr(1);
        function trim(arr) {
          var start = 0;
          for (; start < arr.length; start++) {
            if (arr[start] !== '') break;
          }
          var end = arr.length - 1;
          for (; end >= 0; end--) {
            if (arr[end] !== '') break;
          }
          if (start > end) return [];
          return arr.slice(start, end - start + 1);
        }
        var fromParts = trim(from.split('/'));
        var toParts = trim(to.split('/'));
        var length = Math.min(fromParts.length, toParts.length);
        var samePartsLength = length;
        for (var i = 0; i < length; i++) {
          if (fromParts[i] !== toParts[i]) {
            samePartsLength = i;
            break;
          }
        }
        var outputParts = [];
        for (var i = samePartsLength; i < fromParts.length; i++) {
          outputParts.push('..');
        }
        outputParts = outputParts.concat(toParts.slice(samePartsLength));
        return outputParts.join('/');
      }};
  
  
  /** @type {function(string, boolean=, number=)} */
  function intArrayFromString(stringy, dontAddNull, length) {
    var len = length > 0 ? length : lengthBytesUTF8(stringy)+1;
    var u8array = new Array(len);
    var numBytesWritten = stringToUTF8Array(stringy, u8array, 0, u8array.length);
    if (dontAddNull) u8array.length = numBytesWritten;
    return u8array;
  }
  var TTY = {ttys:[],init:function () {
        // https://github.com/emscripten-core/emscripten/pull/1555
        // if (ENVIRONMENT_IS_NODE) {
        //   // currently, FS.init does not distinguish if process.stdin is a file or TTY
        //   // device, it always assumes it's a TTY device. because of this, we're forcing
        //   // process.stdin to UTF8 encoding to at least make stdin reading compatible
        //   // with text files until FS.init can be refactored.
        //   process.stdin.setEncoding('utf8');
        // }
      },shutdown:function() {
        // https://github.com/emscripten-core/emscripten/pull/1555
        // if (ENVIRONMENT_IS_NODE) {
        //   // inolen: any idea as to why node -e 'process.stdin.read()' wouldn't exit immediately (with process.stdin being a tty)?
        //   // isaacs: because now it's reading from the stream, you've expressed interest in it, so that read() kicks off a _read() which creates a ReadReq operation
        //   // inolen: I thought read() in that case was a synchronous operation that just grabbed some amount of buffered data if it exists?
        //   // isaacs: it is. but it also triggers a _read() call, which calls readStart() on the handle
        //   // isaacs: do process.stdin.pause() and i'd think it'd probably close the pending call
        //   process.stdin.pause();
        // }
      },register:function(dev, ops) {
        TTY.ttys[dev] = { input: [], output: [], ops: ops };
        FS.registerDevice(dev, TTY.stream_ops);
      },stream_ops:{open:function(stream) {
          var tty = TTY.ttys[stream.node.rdev];
          if (!tty) {
            throw new FS.ErrnoError(43);
          }
          stream.tty = tty;
          stream.seekable = false;
        },close:function(stream) {
          // flush any pending line data
          stream.tty.ops.fsync(stream.tty);
        },fsync:function(stream) {
          stream.tty.ops.fsync(stream.tty);
        },read:function(stream, buffer, offset, length, pos /* ignored */) {
          if (!stream.tty || !stream.tty.ops.get_char) {
            throw new FS.ErrnoError(60);
          }
          var bytesRead = 0;
          for (var i = 0; i < length; i++) {
            var result;
            try {
              result = stream.tty.ops.get_char(stream.tty);
            } catch (e) {
              throw new FS.ErrnoError(29);
            }
            if (result === undefined && bytesRead === 0) {
              throw new FS.ErrnoError(6);
            }
            if (result === null || result === undefined) break;
            bytesRead++;
            buffer[offset+i] = result;
          }
          if (bytesRead) {
            stream.node.timestamp = Date.now();
          }
          return bytesRead;
        },write:function(stream, buffer, offset, length, pos) {
          if (!stream.tty || !stream.tty.ops.put_char) {
            throw new FS.ErrnoError(60);
          }
          try {
            for (var i = 0; i < length; i++) {
              stream.tty.ops.put_char(stream.tty, buffer[offset+i]);
            }
          } catch (e) {
            throw new FS.ErrnoError(29);
          }
          if (length) {
            stream.node.timestamp = Date.now();
          }
          return i;
        }},default_tty_ops:{get_char:function(tty) {
          if (!tty.input.length) {
            var result = null;
            if (ENVIRONMENT_IS_NODE) {
              // we will read data by chunks of BUFSIZE
              var BUFSIZE = 256;
              var buf = Buffer.alloc(BUFSIZE);
              var bytesRead = 0;
  
              try {
                bytesRead = fs.readSync(process.stdin.fd, buf, 0, BUFSIZE, -1);
              } catch(e) {
                // Cross-platform differences: on Windows, reading EOF throws an exception, but on other OSes,
                // reading EOF returns 0. Uniformize behavior by treating the EOF exception to return 0.
                if (e.toString().includes('EOF')) bytesRead = 0;
                else throw e;
              }
  
              if (bytesRead > 0) {
                result = buf.slice(0, bytesRead).toString('utf-8');
              } else {
                result = null;
              }
            } else
            if (typeof window != 'undefined' &&
              typeof window.prompt == 'function') {
              // Browser.
              result = window.prompt('Input: ');  // returns null on cancel
              if (result !== null) {
                result += '\n';
              }
            } else if (typeof readline == 'function') {
              // Command line.
              result = readline();
              if (result !== null) {
                result += '\n';
              }
            }
            if (!result) {
              return null;
            }
            tty.input = intArrayFromString(result, true);
          }
          return tty.input.shift();
        },put_char:function(tty, val) {
          if (val === null || val === 10) {
            out(UTF8ArrayToString(tty.output, 0));
            tty.output = [];
          } else {
            if (val != 0) tty.output.push(val); // val == 0 would cut text output off in the middle.
          }
        },fsync:function(tty) {
          if (tty.output && tty.output.length > 0) {
            out(UTF8ArrayToString(tty.output, 0));
            tty.output = [];
          }
        }},default_tty1_ops:{put_char:function(tty, val) {
          if (val === null || val === 10) {
            err(UTF8ArrayToString(tty.output, 0));
            tty.output = [];
          } else {
            if (val != 0) tty.output.push(val);
          }
        },fsync:function(tty) {
          if (tty.output && tty.output.length > 0) {
            err(UTF8ArrayToString(tty.output, 0));
            tty.output = [];
          }
        }}};
  
  
  
  function alignMemory(size, alignment) {
      assert(alignment, "alignment argument is required");
      return Math.ceil(size / alignment) * alignment;
    }
  function mmapAlloc(size) {
      abort('internal error: mmapAlloc called but `emscripten_builtin_memalign` native symbol not exported');
    }
  var MEMFS = {ops_table:null,mount:function(mount) {
        return MEMFS.createNode(null, '/', 16384 | 511 /* 0777 */, 0);
      },createNode:function(parent, name, mode, dev) {
        if (FS.isBlkdev(mode) || FS.isFIFO(mode)) {
          // no supported
          throw new FS.ErrnoError(63);
        }
        if (!MEMFS.ops_table) {
          MEMFS.ops_table = {
            dir: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr,
                lookup: MEMFS.node_ops.lookup,
                mknod: MEMFS.node_ops.mknod,
                rename: MEMFS.node_ops.rename,
                unlink: MEMFS.node_ops.unlink,
                rmdir: MEMFS.node_ops.rmdir,
                readdir: MEMFS.node_ops.readdir,
                symlink: MEMFS.node_ops.symlink
              },
              stream: {
                llseek: MEMFS.stream_ops.llseek
              }
            },
            file: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr
              },
              stream: {
                llseek: MEMFS.stream_ops.llseek,
                read: MEMFS.stream_ops.read,
                write: MEMFS.stream_ops.write,
                allocate: MEMFS.stream_ops.allocate,
                mmap: MEMFS.stream_ops.mmap,
                msync: MEMFS.stream_ops.msync
              }
            },
            link: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr,
                readlink: MEMFS.node_ops.readlink
              },
              stream: {}
            },
            chrdev: {
              node: {
                getattr: MEMFS.node_ops.getattr,
                setattr: MEMFS.node_ops.setattr
              },
              stream: FS.chrdev_stream_ops
            }
          };
        }
        var node = FS.createNode(parent, name, mode, dev);
        if (FS.isDir(node.mode)) {
          node.node_ops = MEMFS.ops_table.dir.node;
          node.stream_ops = MEMFS.ops_table.dir.stream;
          node.contents = {};
        } else if (FS.isFile(node.mode)) {
          node.node_ops = MEMFS.ops_table.file.node;
          node.stream_ops = MEMFS.ops_table.file.stream;
          node.usedBytes = 0; // The actual number of bytes used in the typed array, as opposed to contents.length which gives the whole capacity.
          // When the byte data of the file is populated, this will point to either a typed array, or a normal JS array. Typed arrays are preferred
          // for performance, and used by default. However, typed arrays are not resizable like normal JS arrays are, so there is a small disk size
          // penalty involved for appending file writes that continuously grow a file similar to std::vector capacity vs used -scheme.
          node.contents = null; 
        } else if (FS.isLink(node.mode)) {
          node.node_ops = MEMFS.ops_table.link.node;
          node.stream_ops = MEMFS.ops_table.link.stream;
        } else if (FS.isChrdev(node.mode)) {
          node.node_ops = MEMFS.ops_table.chrdev.node;
          node.stream_ops = MEMFS.ops_table.chrdev.stream;
        }
        node.timestamp = Date.now();
        // add the new node to the parent
        if (parent) {
          parent.contents[name] = node;
          parent.timestamp = node.timestamp;
        }
        return node;
      },getFileDataAsTypedArray:function(node) {
        if (!node.contents) return new Uint8Array(0);
        if (node.contents.subarray) return node.contents.subarray(0, node.usedBytes); // Make sure to not return excess unused bytes.
        return new Uint8Array(node.contents);
      },expandFileStorage:function(node, newCapacity) {
        var prevCapacity = node.contents ? node.contents.length : 0;
        if (prevCapacity >= newCapacity) return; // No need to expand, the storage was already large enough.
        // Don't expand strictly to the given requested limit if it's only a very small increase, but instead geometrically grow capacity.
        // For small filesizes (<1MB), perform size*2 geometric increase, but for large sizes, do a much more conservative size*1.125 increase to
        // avoid overshooting the allocation cap by a very large margin.
        var CAPACITY_DOUBLING_MAX = 1024 * 1024;
        newCapacity = Math.max(newCapacity, (prevCapacity * (prevCapacity < CAPACITY_DOUBLING_MAX ? 2.0 : 1.125)) >>> 0);
        if (prevCapacity != 0) newCapacity = Math.max(newCapacity, 256); // At minimum allocate 256b for each file when expanding.
        var oldContents = node.contents;
        node.contents = new Uint8Array(newCapacity); // Allocate new storage.
        if (node.usedBytes > 0) node.contents.set(oldContents.subarray(0, node.usedBytes), 0); // Copy old data over to the new storage.
      },resizeFileStorage:function(node, newSize) {
        if (node.usedBytes == newSize) return;
        if (newSize == 0) {
          node.contents = null; // Fully decommit when requesting a resize to zero.
          node.usedBytes = 0;
        } else {
          var oldContents = node.contents;
          node.contents = new Uint8Array(newSize); // Allocate new storage.
          if (oldContents) {
            node.contents.set(oldContents.subarray(0, Math.min(newSize, node.usedBytes))); // Copy old data over to the new storage.
          }
          node.usedBytes = newSize;
        }
      },node_ops:{getattr:function(node) {
          var attr = {};
          // device numbers reuse inode numbers.
          attr.dev = FS.isChrdev(node.mode) ? node.id : 1;
          attr.ino = node.id;
          attr.mode = node.mode;
          attr.nlink = 1;
          attr.uid = 0;
          attr.gid = 0;
          attr.rdev = node.rdev;
          if (FS.isDir(node.mode)) {
            attr.size = 4096;
          } else if (FS.isFile(node.mode)) {
            attr.size = node.usedBytes;
          } else if (FS.isLink(node.mode)) {
            attr.size = node.link.length;
          } else {
            attr.size = 0;
          }
          attr.atime = new Date(node.timestamp);
          attr.mtime = new Date(node.timestamp);
          attr.ctime = new Date(node.timestamp);
          // NOTE: In our implementation, st_blocks = Math.ceil(st_size/st_blksize),
          //       but this is not required by the standard.
          attr.blksize = 4096;
          attr.blocks = Math.ceil(attr.size / attr.blksize);
          return attr;
        },setattr:function(node, attr) {
          if (attr.mode !== undefined) {
            node.mode = attr.mode;
          }
          if (attr.timestamp !== undefined) {
            node.timestamp = attr.timestamp;
          }
          if (attr.size !== undefined) {
            MEMFS.resizeFileStorage(node, attr.size);
          }
        },lookup:function(parent, name) {
          throw FS.genericErrors[44];
        },mknod:function(parent, name, mode, dev) {
          return MEMFS.createNode(parent, name, mode, dev);
        },rename:function(old_node, new_dir, new_name) {
          // if we're overwriting a directory at new_name, make sure it's empty.
          if (FS.isDir(old_node.mode)) {
            var new_node;
            try {
              new_node = FS.lookupNode(new_dir, new_name);
            } catch (e) {
            }
            if (new_node) {
              for (var i in new_node.contents) {
                throw new FS.ErrnoError(55);
              }
            }
          }
          // do the internal rewiring
          delete old_node.parent.contents[old_node.name];
          old_node.parent.timestamp = Date.now()
          old_node.name = new_name;
          new_dir.contents[new_name] = old_node;
          new_dir.timestamp = old_node.parent.timestamp;
          old_node.parent = new_dir;
        },unlink:function(parent, name) {
          delete parent.contents[name];
          parent.timestamp = Date.now();
        },rmdir:function(parent, name) {
          var node = FS.lookupNode(parent, name);
          for (var i in node.contents) {
            throw new FS.ErrnoError(55);
          }
          delete parent.contents[name];
          parent.timestamp = Date.now();
        },readdir:function(node) {
          var entries = ['.', '..'];
          for (var key in node.contents) {
            if (!node.contents.hasOwnProperty(key)) {
              continue;
            }
            entries.push(key);
          }
          return entries;
        },symlink:function(parent, newname, oldpath) {
          var node = MEMFS.createNode(parent, newname, 511 /* 0777 */ | 40960, 0);
          node.link = oldpath;
          return node;
        },readlink:function(node) {
          if (!FS.isLink(node.mode)) {
            throw new FS.ErrnoError(28);
          }
          return node.link;
        }},stream_ops:{read:function(stream, buffer, offset, length, position) {
          var contents = stream.node.contents;
          if (position >= stream.node.usedBytes) return 0;
          var size = Math.min(stream.node.usedBytes - position, length);
          assert(size >= 0);
          if (size > 8 && contents.subarray) { // non-trivial, and typed array
            buffer.set(contents.subarray(position, position + size), offset);
          } else {
            for (var i = 0; i < size; i++) buffer[offset + i] = contents[position + i];
          }
          return size;
        },write:function(stream, buffer, offset, length, position, canOwn) {
          // The data buffer should be a typed array view
          assert(!(buffer instanceof ArrayBuffer));
  
          if (!length) return 0;
          var node = stream.node;
          node.timestamp = Date.now();
  
          if (buffer.subarray && (!node.contents || node.contents.subarray)) { // This write is from a typed array to a typed array?
            if (canOwn) {
              assert(position === 0, 'canOwn must imply no weird position inside the file');
              node.contents = buffer.subarray(offset, offset + length);
              node.usedBytes = length;
              return length;
            } else if (node.usedBytes === 0 && position === 0) { // If this is a simple first write to an empty file, do a fast set since we don't need to care about old data.
              node.contents = buffer.slice(offset, offset + length);
              node.usedBytes = length;
              return length;
            } else if (position + length <= node.usedBytes) { // Writing to an already allocated and used subrange of the file?
              node.contents.set(buffer.subarray(offset, offset + length), position);
              return length;
            }
          }
  
          // Appending to an existing file and we need to reallocate, or source data did not come as a typed array.
          MEMFS.expandFileStorage(node, position+length);
          if (node.contents.subarray && buffer.subarray) {
            // Use typed array write which is available.
            node.contents.set(buffer.subarray(offset, offset + length), position);
          } else {
            for (var i = 0; i < length; i++) {
             node.contents[position + i] = buffer[offset + i]; // Or fall back to manual write if not.
            }
          }
          node.usedBytes = Math.max(node.usedBytes, position + length);
          return length;
        },llseek:function(stream, offset, whence) {
          var position = offset;
          if (whence === 1) {
            position += stream.position;
          } else if (whence === 2) {
            if (FS.isFile(stream.node.mode)) {
              position += stream.node.usedBytes;
            }
          }
          if (position < 0) {
            throw new FS.ErrnoError(28);
          }
          return position;
        },allocate:function(stream, offset, length) {
          MEMFS.expandFileStorage(stream.node, offset + length);
          stream.node.usedBytes = Math.max(stream.node.usedBytes, offset + length);
        },mmap:function(stream, length, position, prot, flags) {
          if (!FS.isFile(stream.node.mode)) {
            throw new FS.ErrnoError(43);
          }
          var ptr;
          var allocated;
          var contents = stream.node.contents;
          // Only make a new copy when MAP_PRIVATE is specified.
          if (!(flags & 2) && contents.buffer === HEAP8.buffer) {
            // We can't emulate MAP_SHARED when the file is not backed by the
            // buffer we're mapping to (e.g. the HEAP buffer).
            allocated = false;
            ptr = contents.byteOffset;
          } else {
            // Try to avoid unnecessary slices.
            if (position > 0 || position + length < contents.length) {
              if (contents.subarray) {
                contents = contents.subarray(position, position + length);
              } else {
                contents = Array.prototype.slice.call(contents, position, position + length);
              }
            }
            allocated = true;
            ptr = mmapAlloc(length);
            if (!ptr) {
              throw new FS.ErrnoError(48);
            }
            HEAP8.set(contents, ptr);
          }
          return { ptr: ptr, allocated: allocated };
        },msync:function(stream, buffer, offset, length, mmapFlags) {
          MEMFS.stream_ops.write(stream, buffer, 0, length, offset, false);
          // should we check if bytesWritten and length are the same?
          return 0;
        }}};
  
  /** @param {boolean=} noRunDep */
  function asyncLoad(url, onload, onerror, noRunDep) {
      var dep = !noRunDep ? getUniqueRunDependency('al ' + url) : '';
      readAsync(url, (arrayBuffer) => {
        assert(arrayBuffer, 'Loading data file "' + url + '" failed (no arrayBuffer).');
        onload(new Uint8Array(arrayBuffer));
        if (dep) removeRunDependency(dep);
      }, (event) => {
        if (onerror) {
          onerror();
        } else {
          throw 'Loading data file "' + url + '" failed.';
        }
      });
      if (dep) addRunDependency(dep);
    }
  
  
  var ERRNO_MESSAGES = {0:"Success",1:"Arg list too long",2:"Permission denied",3:"Address already in use",4:"Address not available",5:"Address family not supported by protocol family",6:"No more processes",7:"Socket already connected",8:"Bad file number",9:"Trying to read unreadable message",10:"Mount device busy",11:"Operation canceled",12:"No children",13:"Connection aborted",14:"Connection refused",15:"Connection reset by peer",16:"File locking deadlock error",17:"Destination address required",18:"Math arg out of domain of func",19:"Quota exceeded",20:"File exists",21:"Bad address",22:"File too large",23:"Host is unreachable",24:"Identifier removed",25:"Illegal byte sequence",26:"Connection already in progress",27:"Interrupted system call",28:"Invalid argument",29:"I/O error",30:"Socket is already connected",31:"Is a directory",32:"Too many symbolic links",33:"Too many open files",34:"Too many links",35:"Message too long",36:"Multihop attempted",37:"File or path name too long",38:"Network interface is not configured",39:"Connection reset by network",40:"Network is unreachable",41:"Too many open files in system",42:"No buffer space available",43:"No such device",44:"No such file or directory",45:"Exec format error",46:"No record locks available",47:"The link has been severed",48:"Not enough core",49:"No message of desired type",50:"Protocol not available",51:"No space left on device",52:"Function not implemented",53:"Socket is not connected",54:"Not a directory",55:"Directory not empty",56:"State not recoverable",57:"Socket operation on non-socket",59:"Not a typewriter",60:"No such device or address",61:"Value too large for defined data type",62:"Previous owner died",63:"Not super-user",64:"Broken pipe",65:"Protocol error",66:"Unknown protocol",67:"Protocol wrong type for socket",68:"Math result not representable",69:"Read only file system",70:"Illegal seek",71:"No such process",72:"Stale file handle",73:"Connection timed out",74:"Text file busy",75:"Cross-device link",100:"Device not a stream",101:"Bad font file fmt",102:"Invalid slot",103:"Invalid request code",104:"No anode",105:"Block device required",106:"Channel number out of range",107:"Level 3 halted",108:"Level 3 reset",109:"Link number out of range",110:"Protocol driver not attached",111:"No CSI structure available",112:"Level 2 halted",113:"Invalid exchange",114:"Invalid request descriptor",115:"Exchange full",116:"No data (for no delay io)",117:"Timer expired",118:"Out of streams resources",119:"Machine is not on the network",120:"Package not installed",121:"The object is remote",122:"Advertise error",123:"Srmount error",124:"Communication error on send",125:"Cross mount point (not really error)",126:"Given log. name not unique",127:"f.d. invalid for this operation",128:"Remote address changed",129:"Can   access a needed shared lib",130:"Accessing a corrupted shared lib",131:".lib section in a.out corrupted",132:"Attempting to link in too many libs",133:"Attempting to exec a shared library",135:"Streams pipe error",136:"Too many users",137:"Socket type not supported",138:"Not supported",139:"Protocol family not supported",140:"Can't send after socket shutdown",141:"Too many references",142:"Host is down",148:"No medium (in tape drive)",156:"Level 2 not synchronized"};
  
  var ERRNO_CODES = {};
  
  function withStackSave(f) {
      var stack = stackSave();
      var ret = f();
      stackRestore(stack);
      return ret;
    }
  
  
  function demangle(func) {
      // If demangle has failed before, stop demangling any further function names
      // This avoids an infinite recursion with malloc()->abort()->stackTrace()->demangle()->malloc()->...
      demangle.recursionGuard = (demangle.recursionGuard|0)+1;
      if (demangle.recursionGuard > 1) return func;
      return withStackSave(function() {
        try {
          var s = func;
          if (s.startsWith('__Z'))
            s = s.substr(1);
          var len = lengthBytesUTF8(s)+1;
          var buf = stackAlloc(len);
          stringToUTF8(s, buf, len);
          var status = stackAlloc(4);
          var ret = ___cxa_demangle(buf, 0, 0, status);
          if (HEAP32[((status)>>2)] === 0 && ret) {
            return UTF8ToString(ret);
          }
          // otherwise, libcxxabi failed
        } catch(e) {
        } finally {
          _free(ret);
          if (demangle.recursionGuard < 2) --demangle.recursionGuard;
        }
        // failure when using libcxxabi, don't demangle
        return func;
      });
    }
  function demangleAll(text) {
      var regex =
        /\b_Z[\w\d_]+/g;
      return text.replace(regex,
        function(x) {
          var y = demangle(x);
          return x === y ? x : (y + ' [' + x + ']');
        });
    }
  var FS = {root:null,mounts:[],devices:{},streams:[],nextInode:1,nameTable:null,currentPath:"/",initialized:false,ignorePermissions:true,ErrnoError:null,genericErrors:{},filesystems:null,syncFSRequests:0,lookupPath:(path, opts = {}) => {
        path = PATH_FS.resolve(path);
  
        if (!path) return { path: '', node: null };
  
        var defaults = {
          follow_mount: true,
          recurse_count: 0
        };
        opts = Object.assign(defaults, opts)
  
        if (opts.recurse_count > 8) {  // max recursive lookup of 8
          throw new FS.ErrnoError(32);
        }
  
        // split the absolute path
        var parts = path.split('/').filter((p) => !!p);
  
        // start at the root
        var current = FS.root;
        var current_path = '/';
  
        for (var i = 0; i < parts.length; i++) {
          var islast = (i === parts.length-1);
          if (islast && opts.parent) {
            // stop resolving
            break;
          }
  
          current = FS.lookupNode(current, parts[i]);
          current_path = PATH.join2(current_path, parts[i]);
  
          // jump to the mount's root node if this is a mountpoint
          if (FS.isMountpoint(current)) {
            if (!islast || (islast && opts.follow_mount)) {
              current = current.mounted.root;
            }
          }
  
          // by default, lookupPath will not follow a symlink if it is the final path component.
          // setting opts.follow = true will override this behavior.
          if (!islast || opts.follow) {
            var count = 0;
            while (FS.isLink(current.mode)) {
              var link = FS.readlink(current_path);
              current_path = PATH_FS.resolve(PATH.dirname(current_path), link);
  
              var lookup = FS.lookupPath(current_path, { recurse_count: opts.recurse_count + 1 });
              current = lookup.node;
  
              if (count++ > 40) {  // limit max consecutive symlinks to 40 (SYMLOOP_MAX).
                throw new FS.ErrnoError(32);
              }
            }
          }
        }
  
        return { path: current_path, node: current };
      },getPath:(node) => {
        var path;
        while (true) {
          if (FS.isRoot(node)) {
            var mount = node.mount.mountpoint;
            if (!path) return mount;
            return mount[mount.length-1] !== '/' ? mount + '/' + path : mount + path;
          }
          path = path ? node.name + '/' + path : node.name;
          node = node.parent;
        }
      },hashName:(parentid, name) => {
        var hash = 0;
  
        for (var i = 0; i < name.length; i++) {
          hash = ((hash << 5) - hash + name.charCodeAt(i)) | 0;
        }
        return ((parentid + hash) >>> 0) % FS.nameTable.length;
      },hashAddNode:(node) => {
        var hash = FS.hashName(node.parent.id, node.name);
        node.name_next = FS.nameTable[hash];
        FS.nameTable[hash] = node;
      },hashRemoveNode:(node) => {
        var hash = FS.hashName(node.parent.id, node.name);
        if (FS.nameTable[hash] === node) {
          FS.nameTable[hash] = node.name_next;
        } else {
          var current = FS.nameTable[hash];
          while (current) {
            if (current.name_next === node) {
              current.name_next = node.name_next;
              break;
            }
            current = current.name_next;
          }
        }
      },lookupNode:(parent, name) => {
        var errCode = FS.mayLookup(parent);
        if (errCode) {
          throw new FS.ErrnoError(errCode, parent);
        }
        var hash = FS.hashName(parent.id, name);
        for (var node = FS.nameTable[hash]; node; node = node.name_next) {
          var nodeName = node.name;
          if (node.parent.id === parent.id && nodeName === name) {
            return node;
          }
        }
        // if we failed to find it in the cache, call into the VFS
        return FS.lookup(parent, name);
      },createNode:(parent, name, mode, rdev) => {
        assert(typeof parent == 'object')
        var node = new FS.FSNode(parent, name, mode, rdev);
  
        FS.hashAddNode(node);
  
        return node;
      },destroyNode:(node) => {
        FS.hashRemoveNode(node);
      },isRoot:(node) => {
        return node === node.parent;
      },isMountpoint:(node) => {
        return !!node.mounted;
      },isFile:(mode) => {
        return (mode & 61440) === 32768;
      },isDir:(mode) => {
        return (mode & 61440) === 16384;
      },isLink:(mode) => {
        return (mode & 61440) === 40960;
      },isChrdev:(mode) => {
        return (mode & 61440) === 8192;
      },isBlkdev:(mode) => {
        return (mode & 61440) === 24576;
      },isFIFO:(mode) => {
        return (mode & 61440) === 4096;
      },isSocket:(mode) => {
        return (mode & 49152) === 49152;
      },flagModes:{"r":0,"r+":2,"w":577,"w+":578,"a":1089,"a+":1090},modeStringToFlags:(str) => {
        var flags = FS.flagModes[str];
        if (typeof flags == 'undefined') {
          throw new Error('Unknown file open mode: ' + str);
        }
        return flags;
      },flagsToPermissionString:(flag) => {
        var perms = ['r', 'w', 'rw'][flag & 3];
        if ((flag & 512)) {
          perms += 'w';
        }
        return perms;
      },nodePermissions:(node, perms) => {
        if (FS.ignorePermissions) {
          return 0;
        }
        // return 0 if any user, group or owner bits are set.
        if (perms.includes('r') && !(node.mode & 292)) {
          return 2;
        } else if (perms.includes('w') && !(node.mode & 146)) {
          return 2;
        } else if (perms.includes('x') && !(node.mode & 73)) {
          return 2;
        }
        return 0;
      },mayLookup:(dir) => {
        var errCode = FS.nodePermissions(dir, 'x');
        if (errCode) return errCode;
        if (!dir.node_ops.lookup) return 2;
        return 0;
      },mayCreate:(dir, name) => {
        try {
          var node = FS.lookupNode(dir, name);
          return 20;
        } catch (e) {
        }
        return FS.nodePermissions(dir, 'wx');
      },mayDelete:(dir, name, isdir) => {
        var node;
        try {
          node = FS.lookupNode(dir, name);
        } catch (e) {
          return e.errno;
        }
        var errCode = FS.nodePermissions(dir, 'wx');
        if (errCode) {
          return errCode;
        }
        if (isdir) {
          if (!FS.isDir(node.mode)) {
            return 54;
          }
          if (FS.isRoot(node) || FS.getPath(node) === FS.cwd()) {
            return 10;
          }
        } else {
          if (FS.isDir(node.mode)) {
            return 31;
          }
        }
        return 0;
      },mayOpen:(node, flags) => {
        if (!node) {
          return 44;
        }
        if (FS.isLink(node.mode)) {
          return 32;
        } else if (FS.isDir(node.mode)) {
          if (FS.flagsToPermissionString(flags) !== 'r' || // opening for write
              (flags & 512)) { // TODO: check for O_SEARCH? (== search for dir only)
            return 31;
          }
        }
        return FS.nodePermissions(node, FS.flagsToPermissionString(flags));
      },MAX_OPEN_FDS:4096,nextfd:(fd_start = 0, fd_end = FS.MAX_OPEN_FDS) => {
        for (var fd = fd_start; fd <= fd_end; fd++) {
          if (!FS.streams[fd]) {
            return fd;
          }
        }
        throw new FS.ErrnoError(33);
      },getStream:(fd) => FS.streams[fd],createStream:(stream, fd_start, fd_end) => {
        if (!FS.FSStream) {
          FS.FSStream = /** @constructor */ function() {
            this.shared = { };
          };
          FS.FSStream.prototype = {};
          Object.defineProperties(FS.FSStream.prototype, {
            object: {
              /** @this {FS.FSStream} */
              get: function() { return this.node; },
              /** @this {FS.FSStream} */
              set: function(val) { this.node = val; }
            },
            isRead: {
              /** @this {FS.FSStream} */
              get: function() { return (this.flags & 2097155) !== 1; }
            },
            isWrite: {
              /** @this {FS.FSStream} */
              get: function() { return (this.flags & 2097155) !== 0; }
            },
            isAppend: {
              /** @this {FS.FSStream} */
              get: function() { return (this.flags & 1024); }
            },
            flags: {
              /** @this {FS.FSStream} */
              get: function() { return this.shared.flags; },
              /** @this {FS.FSStream} */
              set: function(val) { this.shared.flags = val; },
            },
            position : {
              /** @this {FS.FSStream} */
              get: function() { return this.shared.position; },
              /** @this {FS.FSStream} */
              set: function(val) { this.shared.position = val; },
            },
          });
        }
        // clone it, so we can return an instance of FSStream
        stream = Object.assign(new FS.FSStream(), stream);
        var fd = FS.nextfd(fd_start, fd_end);
        stream.fd = fd;
        FS.streams[fd] = stream;
        return stream;
      },closeStream:(fd) => {
        FS.streams[fd] = null;
      },chrdev_stream_ops:{open:(stream) => {
          var device = FS.getDevice(stream.node.rdev);
          // override node's stream ops with the device's
          stream.stream_ops = device.stream_ops;
          // forward the open call
          if (stream.stream_ops.open) {
            stream.stream_ops.open(stream);
          }
        },llseek:() => {
          throw new FS.ErrnoError(70);
        }},major:(dev) => ((dev) >> 8),minor:(dev) => ((dev) & 0xff),makedev:(ma, mi) => ((ma) << 8 | (mi)),registerDevice:(dev, ops) => {
        FS.devices[dev] = { stream_ops: ops };
      },getDevice:(dev) => FS.devices[dev],getMounts:(mount) => {
        var mounts = [];
        var check = [mount];
  
        while (check.length) {
          var m = check.pop();
  
          mounts.push(m);
  
          check.push.apply(check, m.mounts);
        }
  
        return mounts;
      },syncfs:(populate, callback) => {
        if (typeof populate == 'function') {
          callback = populate;
          populate = false;
        }
  
        FS.syncFSRequests++;
  
        if (FS.syncFSRequests > 1) {
          err('warning: ' + FS.syncFSRequests + ' FS.syncfs operations in flight at once, probably just doing extra work');
        }
  
        var mounts = FS.getMounts(FS.root.mount);
        var completed = 0;
  
        function doCallback(errCode) {
          assert(FS.syncFSRequests > 0);
          FS.syncFSRequests--;
          return callback(errCode);
        }
  
        function done(errCode) {
          if (errCode) {
            if (!done.errored) {
              done.errored = true;
              return doCallback(errCode);
            }
            return;
          }
          if (++completed >= mounts.length) {
            doCallback(null);
          }
        };
  
        // sync all mounts
        mounts.forEach((mount) => {
          if (!mount.type.syncfs) {
            return done(null);
          }
          mount.type.syncfs(mount, populate, done);
        });
      },mount:(type, opts, mountpoint) => {
        if (typeof type == 'string') {
          // The filesystem was not included, and instead we have an error
          // message stored in the variable.
          throw type;
        }
        var root = mountpoint === '/';
        var pseudo = !mountpoint;
        var node;
  
        if (root && FS.root) {
          throw new FS.ErrnoError(10);
        } else if (!root && !pseudo) {
          var lookup = FS.lookupPath(mountpoint, { follow_mount: false });
  
          mountpoint = lookup.path;  // use the absolute path
          node = lookup.node;
  
          if (FS.isMountpoint(node)) {
            throw new FS.ErrnoError(10);
          }
  
          if (!FS.isDir(node.mode)) {
            throw new FS.ErrnoError(54);
          }
        }
  
        var mount = {
          type: type,
          opts: opts,
          mountpoint: mountpoint,
          mounts: []
        };
  
        // create a root node for the fs
        var mountRoot = type.mount(mount);
        mountRoot.mount = mount;
        mount.root = mountRoot;
  
        if (root) {
          FS.root = mountRoot;
        } else if (node) {
          // set as a mountpoint
          node.mounted = mount;
  
          // add the new mount to the current mount's children
          if (node.mount) {
            node.mount.mounts.push(mount);
          }
        }
  
        return mountRoot;
      },unmount:(mountpoint) => {
        var lookup = FS.lookupPath(mountpoint, { follow_mount: false });
  
        if (!FS.isMountpoint(lookup.node)) {
          throw new FS.ErrnoError(28);
        }
  
        // destroy the nodes for this mount, and all its child mounts
        var node = lookup.node;
        var mount = node.mounted;
        var mounts = FS.getMounts(mount);
  
        Object.keys(FS.nameTable).forEach((hash) => {
          var current = FS.nameTable[hash];
  
          while (current) {
            var next = current.name_next;
  
            if (mounts.includes(current.mount)) {
              FS.destroyNode(current);
            }
  
            current = next;
          }
        });
  
        // no longer a mountpoint
        node.mounted = null;
  
        // remove this mount from the child mounts
        var idx = node.mount.mounts.indexOf(mount);
        assert(idx !== -1);
        node.mount.mounts.splice(idx, 1);
      },lookup:(parent, name) => {
        return parent.node_ops.lookup(parent, name);
      },mknod:(path, mode, dev) => {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        var name = PATH.basename(path);
        if (!name || name === '.' || name === '..') {
          throw new FS.ErrnoError(28);
        }
        var errCode = FS.mayCreate(parent, name);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.mknod) {
          throw new FS.ErrnoError(63);
        }
        return parent.node_ops.mknod(parent, name, mode, dev);
      },create:(path, mode) => {
        mode = mode !== undefined ? mode : 438 /* 0666 */;
        mode &= 4095;
        mode |= 32768;
        return FS.mknod(path, mode, 0);
      },mkdir:(path, mode) => {
        mode = mode !== undefined ? mode : 511 /* 0777 */;
        mode &= 511 | 512;
        mode |= 16384;
        return FS.mknod(path, mode, 0);
      },mkdirTree:(path, mode) => {
        var dirs = path.split('/');
        var d = '';
        for (var i = 0; i < dirs.length; ++i) {
          if (!dirs[i]) continue;
          d += '/' + dirs[i];
          try {
            FS.mkdir(d, mode);
          } catch(e) {
            if (e.errno != 20) throw e;
          }
        }
      },mkdev:(path, mode, dev) => {
        if (typeof dev == 'undefined') {
          dev = mode;
          mode = 438 /* 0666 */;
        }
        mode |= 8192;
        return FS.mknod(path, mode, dev);
      },symlink:(oldpath, newpath) => {
        if (!PATH_FS.resolve(oldpath)) {
          throw new FS.ErrnoError(44);
        }
        var lookup = FS.lookupPath(newpath, { parent: true });
        var parent = lookup.node;
        if (!parent) {
          throw new FS.ErrnoError(44);
        }
        var newname = PATH.basename(newpath);
        var errCode = FS.mayCreate(parent, newname);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.symlink) {
          throw new FS.ErrnoError(63);
        }
        return parent.node_ops.symlink(parent, newname, oldpath);
      },rename:(old_path, new_path) => {
        var old_dirname = PATH.dirname(old_path);
        var new_dirname = PATH.dirname(new_path);
        var old_name = PATH.basename(old_path);
        var new_name = PATH.basename(new_path);
        // parents must exist
        var lookup, old_dir, new_dir;
  
        // let the errors from non existant directories percolate up
        lookup = FS.lookupPath(old_path, { parent: true });
        old_dir = lookup.node;
        lookup = FS.lookupPath(new_path, { parent: true });
        new_dir = lookup.node;
  
        if (!old_dir || !new_dir) throw new FS.ErrnoError(44);
        // need to be part of the same mount
        if (old_dir.mount !== new_dir.mount) {
          throw new FS.ErrnoError(75);
        }
        // source must exist
        var old_node = FS.lookupNode(old_dir, old_name);
        // old path should not be an ancestor of the new path
        var relative = PATH_FS.relative(old_path, new_dirname);
        if (relative.charAt(0) !== '.') {
          throw new FS.ErrnoError(28);
        }
        // new path should not be an ancestor of the old path
        relative = PATH_FS.relative(new_path, old_dirname);
        if (relative.charAt(0) !== '.') {
          throw new FS.ErrnoError(55);
        }
        // see if the new path already exists
        var new_node;
        try {
          new_node = FS.lookupNode(new_dir, new_name);
        } catch (e) {
          // not fatal
        }
        // early out if nothing needs to change
        if (old_node === new_node) {
          return;
        }
        // we'll need to delete the old entry
        var isdir = FS.isDir(old_node.mode);
        var errCode = FS.mayDelete(old_dir, old_name, isdir);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        // need delete permissions if we'll be overwriting.
        // need create permissions if new doesn't already exist.
        errCode = new_node ?
          FS.mayDelete(new_dir, new_name, isdir) :
          FS.mayCreate(new_dir, new_name);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!old_dir.node_ops.rename) {
          throw new FS.ErrnoError(63);
        }
        if (FS.isMountpoint(old_node) || (new_node && FS.isMountpoint(new_node))) {
          throw new FS.ErrnoError(10);
        }
        // if we are going to change the parent, check write permissions
        if (new_dir !== old_dir) {
          errCode = FS.nodePermissions(old_dir, 'w');
          if (errCode) {
            throw new FS.ErrnoError(errCode);
          }
        }
        // remove the node from the lookup hash
        FS.hashRemoveNode(old_node);
        // do the underlying fs rename
        try {
          old_dir.node_ops.rename(old_node, new_dir, new_name);
        } catch (e) {
          throw e;
        } finally {
          // add the node back to the hash (in case node_ops.rename
          // changed its name)
          FS.hashAddNode(old_node);
        }
      },rmdir:(path) => {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var errCode = FS.mayDelete(parent, name, true);
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.rmdir) {
          throw new FS.ErrnoError(63);
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(10);
        }
        parent.node_ops.rmdir(parent, name);
        FS.destroyNode(node);
      },readdir:(path) => {
        var lookup = FS.lookupPath(path, { follow: true });
        var node = lookup.node;
        if (!node.node_ops.readdir) {
          throw new FS.ErrnoError(54);
        }
        return node.node_ops.readdir(node);
      },unlink:(path) => {
        var lookup = FS.lookupPath(path, { parent: true });
        var parent = lookup.node;
        if (!parent) {
          throw new FS.ErrnoError(44);
        }
        var name = PATH.basename(path);
        var node = FS.lookupNode(parent, name);
        var errCode = FS.mayDelete(parent, name, false);
        if (errCode) {
          // According to POSIX, we should map EISDIR to EPERM, but
          // we instead do what Linux does (and we must, as we use
          // the musl linux libc).
          throw new FS.ErrnoError(errCode);
        }
        if (!parent.node_ops.unlink) {
          throw new FS.ErrnoError(63);
        }
        if (FS.isMountpoint(node)) {
          throw new FS.ErrnoError(10);
        }
        parent.node_ops.unlink(parent, name);
        FS.destroyNode(node);
      },readlink:(path) => {
        var lookup = FS.lookupPath(path);
        var link = lookup.node;
        if (!link) {
          throw new FS.ErrnoError(44);
        }
        if (!link.node_ops.readlink) {
          throw new FS.ErrnoError(28);
        }
        return PATH_FS.resolve(FS.getPath(link.parent), link.node_ops.readlink(link));
      },stat:(path, dontFollow) => {
        var lookup = FS.lookupPath(path, { follow: !dontFollow });
        var node = lookup.node;
        if (!node) {
          throw new FS.ErrnoError(44);
        }
        if (!node.node_ops.getattr) {
          throw new FS.ErrnoError(63);
        }
        return node.node_ops.getattr(node);
      },lstat:(path) => {
        return FS.stat(path, true);
      },chmod:(path, mode, dontFollow) => {
        var node;
        if (typeof path == 'string') {
          var lookup = FS.lookupPath(path, { follow: !dontFollow });
          node = lookup.node;
        } else {
          node = path;
        }
        if (!node.node_ops.setattr) {
          throw new FS.ErrnoError(63);
        }
        node.node_ops.setattr(node, {
          mode: (mode & 4095) | (node.mode & ~4095),
          timestamp: Date.now()
        });
      },lchmod:(path, mode) => {
        FS.chmod(path, mode, true);
      },fchmod:(fd, mode) => {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(8);
        }
        FS.chmod(stream.node, mode);
      },chown:(path, uid, gid, dontFollow) => {
        var node;
        if (typeof path == 'string') {
          var lookup = FS.lookupPath(path, { follow: !dontFollow });
          node = lookup.node;
        } else {
          node = path;
        }
        if (!node.node_ops.setattr) {
          throw new FS.ErrnoError(63);
        }
        node.node_ops.setattr(node, {
          timestamp: Date.now()
          // we ignore the uid / gid for now
        });
      },lchown:(path, uid, gid) => {
        FS.chown(path, uid, gid, true);
      },fchown:(fd, uid, gid) => {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(8);
        }
        FS.chown(stream.node, uid, gid);
      },truncate:(path, len) => {
        if (len < 0) {
          throw new FS.ErrnoError(28);
        }
        var node;
        if (typeof path == 'string') {
          var lookup = FS.lookupPath(path, { follow: true });
          node = lookup.node;
        } else {
          node = path;
        }
        if (!node.node_ops.setattr) {
          throw new FS.ErrnoError(63);
        }
        if (FS.isDir(node.mode)) {
          throw new FS.ErrnoError(31);
        }
        if (!FS.isFile(node.mode)) {
          throw new FS.ErrnoError(28);
        }
        var errCode = FS.nodePermissions(node, 'w');
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        node.node_ops.setattr(node, {
          size: len,
          timestamp: Date.now()
        });
      },ftruncate:(fd, len) => {
        var stream = FS.getStream(fd);
        if (!stream) {
          throw new FS.ErrnoError(8);
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(28);
        }
        FS.truncate(stream.node, len);
      },utime:(path, atime, mtime) => {
        var lookup = FS.lookupPath(path, { follow: true });
        var node = lookup.node;
        node.node_ops.setattr(node, {
          timestamp: Math.max(atime, mtime)
        });
      },open:(path, flags, mode) => {
        if (path === "") {
          throw new FS.ErrnoError(44);
        }
        flags = typeof flags == 'string' ? FS.modeStringToFlags(flags) : flags;
        mode = typeof mode == 'undefined' ? 438 /* 0666 */ : mode;
        if ((flags & 64)) {
          mode = (mode & 4095) | 32768;
        } else {
          mode = 0;
        }
        var node;
        if (typeof path == 'object') {
          node = path;
        } else {
          path = PATH.normalize(path);
          try {
            var lookup = FS.lookupPath(path, {
              follow: !(flags & 131072)
            });
            node = lookup.node;
          } catch (e) {
            // ignore
          }
        }
        // perhaps we need to create the node
        var created = false;
        if ((flags & 64)) {
          if (node) {
            // if O_CREAT and O_EXCL are set, error out if the node already exists
            if ((flags & 128)) {
              throw new FS.ErrnoError(20);
            }
          } else {
            // node doesn't exist, try to create it
            node = FS.mknod(path, mode, 0);
            created = true;
          }
        }
        if (!node) {
          throw new FS.ErrnoError(44);
        }
        // can't truncate a device
        if (FS.isChrdev(node.mode)) {
          flags &= ~512;
        }
        // if asked only for a directory, then this must be one
        if ((flags & 65536) && !FS.isDir(node.mode)) {
          throw new FS.ErrnoError(54);
        }
        // check permissions, if this is not a file we just created now (it is ok to
        // create and write to a file with read-only permissions; it is read-only
        // for later use)
        if (!created) {
          var errCode = FS.mayOpen(node, flags);
          if (errCode) {
            throw new FS.ErrnoError(errCode);
          }
        }
        // do truncation if necessary
        if ((flags & 512) && !created) {
          FS.truncate(node, 0);
        }
        // we've already handled these, don't pass down to the underlying vfs
        flags &= ~(128 | 512 | 131072);
  
        // register the stream with the filesystem
        var stream = FS.createStream({
          node: node,
          path: FS.getPath(node),  // we want the absolute path to the node
          flags: flags,
          seekable: true,
          position: 0,
          stream_ops: node.stream_ops,
          // used by the file family libc calls (fopen, fwrite, ferror, etc.)
          ungotten: [],
          error: false
        });
        // call the new stream's open function
        if (stream.stream_ops.open) {
          stream.stream_ops.open(stream);
        }
        if (Module['logReadFiles'] && !(flags & 1)) {
          if (!FS.readFiles) FS.readFiles = {};
          if (!(path in FS.readFiles)) {
            FS.readFiles[path] = 1;
          }
        }
        return stream;
      },close:(stream) => {
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if (stream.getdents) stream.getdents = null; // free readdir state
        try {
          if (stream.stream_ops.close) {
            stream.stream_ops.close(stream);
          }
        } catch (e) {
          throw e;
        } finally {
          FS.closeStream(stream.fd);
        }
        stream.fd = null;
      },isClosed:(stream) => {
        return stream.fd === null;
      },llseek:(stream, offset, whence) => {
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if (!stream.seekable || !stream.stream_ops.llseek) {
          throw new FS.ErrnoError(70);
        }
        if (whence != 0 && whence != 1 && whence != 2) {
          throw new FS.ErrnoError(28);
        }
        stream.position = stream.stream_ops.llseek(stream, offset, whence);
        stream.ungotten = [];
        return stream.position;
      },read:(stream, buffer, offset, length, position) => {
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(28);
        }
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(8);
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(31);
        }
        if (!stream.stream_ops.read) {
          throw new FS.ErrnoError(28);
        }
        var seeking = typeof position != 'undefined';
        if (!seeking) {
          position = stream.position;
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(70);
        }
        var bytesRead = stream.stream_ops.read(stream, buffer, offset, length, position);
        if (!seeking) stream.position += bytesRead;
        return bytesRead;
      },write:(stream, buffer, offset, length, position, canOwn) => {
        if (length < 0 || position < 0) {
          throw new FS.ErrnoError(28);
        }
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(8);
        }
        if (FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(31);
        }
        if (!stream.stream_ops.write) {
          throw new FS.ErrnoError(28);
        }
        if (stream.seekable && stream.flags & 1024) {
          // seek to the end before writing in append mode
          FS.llseek(stream, 0, 2);
        }
        var seeking = typeof position != 'undefined';
        if (!seeking) {
          position = stream.position;
        } else if (!stream.seekable) {
          throw new FS.ErrnoError(70);
        }
        var bytesWritten = stream.stream_ops.write(stream, buffer, offset, length, position, canOwn);
        if (!seeking) stream.position += bytesWritten;
        return bytesWritten;
      },allocate:(stream, offset, length) => {
        if (FS.isClosed(stream)) {
          throw new FS.ErrnoError(8);
        }
        if (offset < 0 || length <= 0) {
          throw new FS.ErrnoError(28);
        }
        if ((stream.flags & 2097155) === 0) {
          throw new FS.ErrnoError(8);
        }
        if (!FS.isFile(stream.node.mode) && !FS.isDir(stream.node.mode)) {
          throw new FS.ErrnoError(43);
        }
        if (!stream.stream_ops.allocate) {
          throw new FS.ErrnoError(138);
        }
        stream.stream_ops.allocate(stream, offset, length);
      },mmap:(stream, length, position, prot, flags) => {
        // User requests writing to file (prot & PROT_WRITE != 0).
        // Checking if we have permissions to write to the file unless
        // MAP_PRIVATE flag is set. According to POSIX spec it is possible
        // to write to file opened in read-only mode with MAP_PRIVATE flag,
        // as all modifications will be visible only in the memory of
        // the current process.
        if ((prot & 2) !== 0
            && (flags & 2) === 0
            && (stream.flags & 2097155) !== 2) {
          throw new FS.ErrnoError(2);
        }
        if ((stream.flags & 2097155) === 1) {
          throw new FS.ErrnoError(2);
        }
        if (!stream.stream_ops.mmap) {
          throw new FS.ErrnoError(43);
        }
        return stream.stream_ops.mmap(stream, length, position, prot, flags);
      },msync:(stream, buffer, offset, length, mmapFlags) => {
        if (!stream.stream_ops.msync) {
          return 0;
        }
        return stream.stream_ops.msync(stream, buffer, offset, length, mmapFlags);
      },munmap:(stream) => 0,ioctl:(stream, cmd, arg) => {
        if (!stream.stream_ops.ioctl) {
          throw new FS.ErrnoError(59);
        }
        return stream.stream_ops.ioctl(stream, cmd, arg);
      },readFile:(path, opts = {}) => {
        opts.flags = opts.flags || 0;
        opts.encoding = opts.encoding || 'binary';
        if (opts.encoding !== 'utf8' && opts.encoding !== 'binary') {
          throw new Error('Invalid encoding type "' + opts.encoding + '"');
        }
        var ret;
        var stream = FS.open(path, opts.flags);
        var stat = FS.stat(path);
        var length = stat.size;
        var buf = new Uint8Array(length);
        FS.read(stream, buf, 0, length, 0);
        if (opts.encoding === 'utf8') {
          ret = UTF8ArrayToString(buf, 0);
        } else if (opts.encoding === 'binary') {
          ret = buf;
        }
        FS.close(stream);
        return ret;
      },writeFile:(path, data, opts = {}) => {
        opts.flags = opts.flags || 577;
        var stream = FS.open(path, opts.flags, opts.mode);
        if (typeof data == 'string') {
          var buf = new Uint8Array(lengthBytesUTF8(data)+1);
          var actualNumBytes = stringToUTF8Array(data, buf, 0, buf.length);
          FS.write(stream, buf, 0, actualNumBytes, undefined, opts.canOwn);
        } else if (ArrayBuffer.isView(data)) {
          FS.write(stream, data, 0, data.byteLength, undefined, opts.canOwn);
        } else {
          throw new Error('Unsupported data type');
        }
        FS.close(stream);
      },cwd:() => FS.currentPath,chdir:(path) => {
        var lookup = FS.lookupPath(path, { follow: true });
        if (lookup.node === null) {
          throw new FS.ErrnoError(44);
        }
        if (!FS.isDir(lookup.node.mode)) {
          throw new FS.ErrnoError(54);
        }
        var errCode = FS.nodePermissions(lookup.node, 'x');
        if (errCode) {
          throw new FS.ErrnoError(errCode);
        }
        FS.currentPath = lookup.path;
      },createDefaultDirectories:() => {
        FS.mkdir('/tmp');
        FS.mkdir('/home');
        FS.mkdir('/home/web_user');
      },createDefaultDevices:() => {
        // create /dev
        FS.mkdir('/dev');
        // setup /dev/null
        FS.registerDevice(FS.makedev(1, 3), {
          read: () => 0,
          write: (stream, buffer, offset, length, pos) => length,
        });
        FS.mkdev('/dev/null', FS.makedev(1, 3));
        // setup /dev/tty and /dev/tty1
        // stderr needs to print output using err() rather than out()
        // so we register a second tty just for it.
        TTY.register(FS.makedev(5, 0), TTY.default_tty_ops);
        TTY.register(FS.makedev(6, 0), TTY.default_tty1_ops);
        FS.mkdev('/dev/tty', FS.makedev(5, 0));
        FS.mkdev('/dev/tty1', FS.makedev(6, 0));
        // setup /dev/[u]random
        var random_device = getRandomDevice();
        FS.createDevice('/dev', 'random', random_device);
        FS.createDevice('/dev', 'urandom', random_device);
        // we're not going to emulate the actual shm device,
        // just create the tmp dirs that reside in it commonly
        FS.mkdir('/dev/shm');
        FS.mkdir('/dev/shm/tmp');
      },createSpecialDirectories:() => {
        // create /proc/self/fd which allows /proc/self/fd/6 => readlink gives the
        // name of the stream for fd 6 (see test_unistd_ttyname)
        FS.mkdir('/proc');
        var proc_self = FS.mkdir('/proc/self');
        FS.mkdir('/proc/self/fd');
        FS.mount({
          mount: () => {
            var node = FS.createNode(proc_self, 'fd', 16384 | 511 /* 0777 */, 73);
            node.node_ops = {
              lookup: (parent, name) => {
                var fd = +name;
                var stream = FS.getStream(fd);
                if (!stream) throw new FS.ErrnoError(8);
                var ret = {
                  parent: null,
                  mount: { mountpoint: 'fake' },
                  node_ops: { readlink: () => stream.path },
                };
                ret.parent = ret; // make it look like a simple root node
                return ret;
              }
            };
            return node;
          }
        }, {}, '/proc/self/fd');
      },createStandardStreams:() => {
        // TODO deprecate the old functionality of a single
        // input / output callback and that utilizes FS.createDevice
        // and instead require a unique set of stream ops
  
        // by default, we symlink the standard streams to the
        // default tty devices. however, if the standard streams
        // have been overwritten we create a unique device for
        // them instead.
        if (Module['stdin']) {
          FS.createDevice('/dev', 'stdin', Module['stdin']);
        } else {
          FS.symlink('/dev/tty', '/dev/stdin');
        }
        if (Module['stdout']) {
          FS.createDevice('/dev', 'stdout', null, Module['stdout']);
        } else {
          FS.symlink('/dev/tty', '/dev/stdout');
        }
        if (Module['stderr']) {
          FS.createDevice('/dev', 'stderr', null, Module['stderr']);
        } else {
          FS.symlink('/dev/tty1', '/dev/stderr');
        }
  
        // open default streams for the stdin, stdout and stderr devices
        var stdin = FS.open('/dev/stdin', 0);
        var stdout = FS.open('/dev/stdout', 1);
        var stderr = FS.open('/dev/stderr', 1);
        assert(stdin.fd === 0, 'invalid handle for stdin (' + stdin.fd + ')');
        assert(stdout.fd === 1, 'invalid handle for stdout (' + stdout.fd + ')');
        assert(stderr.fd === 2, 'invalid handle for stderr (' + stderr.fd + ')');
      },ensureErrnoError:() => {
        if (FS.ErrnoError) return;
        FS.ErrnoError = /** @this{Object} */ function ErrnoError(errno, node) {
          // We set the `name` property to be able to identify `FS.ErrnoError`
          // - the `name` is a standard ECMA-262 property of error objects. Kind of good to have it anyway.
          // - when using PROXYFS, an error can come from an underlying FS
          // as different FS objects have their own FS.ErrnoError each,
          // the test `err instanceof FS.ErrnoError` won't detect an error coming from another filesystem, causing bugs.
          // we'll use the reliable test `err.name == "ErrnoError"` instead
          this.name = 'ErrnoError';
          this.node = node;
          this.setErrno = /** @this{Object} */ function(errno) {
            this.errno = errno;
            for (var key in ERRNO_CODES) {
              if (ERRNO_CODES[key] === errno) {
                this.code = key;
                break;
              }
            }
          };
          this.setErrno(errno);
          this.message = ERRNO_MESSAGES[errno];
  
          // Try to get a maximally helpful stack trace. On Node.js, getting Error.stack
          // now ensures it shows what we want.
          if (this.stack) {
            // Define the stack property for Node.js 4, which otherwise errors on the next line.
            Object.defineProperty(this, "stack", { value: (new Error).stack, writable: true });
            this.stack = demangleAll(this.stack);
          }
        };
        FS.ErrnoError.prototype = new Error();
        FS.ErrnoError.prototype.constructor = FS.ErrnoError;
        // Some errors may happen quite a bit, to avoid overhead we reuse them (and suffer a lack of stack info)
        [44].forEach((code) => {
          FS.genericErrors[code] = new FS.ErrnoError(code);
          FS.genericErrors[code].stack = '<generic error, no stack>';
        });
      },staticInit:() => {
        FS.ensureErrnoError();
  
        FS.nameTable = new Array(4096);
  
        FS.mount(MEMFS, {}, '/');
  
        FS.createDefaultDirectories();
        FS.createDefaultDevices();
        FS.createSpecialDirectories();
  
        FS.filesystems = {
          'MEMFS': MEMFS,
        };
      },init:(input, output, error) => {
        assert(!FS.init.initialized, 'FS.init was previously called. If you want to initialize later with custom parameters, remove any earlier calls (note that one is automatically added to the generated code)');
        FS.init.initialized = true;
  
        FS.ensureErrnoError();
  
        // Allow Module.stdin etc. to provide defaults, if none explicitly passed to us here
        Module['stdin'] = input || Module['stdin'];
        Module['stdout'] = output || Module['stdout'];
        Module['stderr'] = error || Module['stderr'];
  
        FS.createStandardStreams();
      },quit:() => {
        FS.init.initialized = false;
        // force-flush all streams, so we get musl std streams printed out
        _fflush(0);
        // close all of our streams
        for (var i = 0; i < FS.streams.length; i++) {
          var stream = FS.streams[i];
          if (!stream) {
            continue;
          }
          FS.close(stream);
        }
      },getMode:(canRead, canWrite) => {
        var mode = 0;
        if (canRead) mode |= 292 | 73;
        if (canWrite) mode |= 146;
        return mode;
      },findObject:(path, dontResolveLastLink) => {
        var ret = FS.analyzePath(path, dontResolveLastLink);
        if (!ret.exists) {
          return null;
        }
        return ret.object;
      },analyzePath:(path, dontResolveLastLink) => {
        // operate from within the context of the symlink's target
        try {
          var lookup = FS.lookupPath(path, { follow: !dontResolveLastLink });
          path = lookup.path;
        } catch (e) {
        }
        var ret = {
          isRoot: false, exists: false, error: 0, name: null, path: null, object: null,
          parentExists: false, parentPath: null, parentObject: null
        };
        try {
          var lookup = FS.lookupPath(path, { parent: true });
          ret.parentExists = true;
          ret.parentPath = lookup.path;
          ret.parentObject = lookup.node;
          ret.name = PATH.basename(path);
          lookup = FS.lookupPath(path, { follow: !dontResolveLastLink });
          ret.exists = true;
          ret.path = lookup.path;
          ret.object = lookup.node;
          ret.name = lookup.node.name;
          ret.isRoot = lookup.path === '/';
        } catch (e) {
          ret.error = e.errno;
        };
        return ret;
      },createPath:(parent, path, canRead, canWrite) => {
        parent = typeof parent == 'string' ? parent : FS.getPath(parent);
        var parts = path.split('/').reverse();
        while (parts.length) {
          var part = parts.pop();
          if (!part) continue;
          var current = PATH.join2(parent, part);
          try {
            FS.mkdir(current);
          } catch (e) {
            // ignore EEXIST
          }
          parent = current;
        }
        return current;
      },createFile:(parent, name, properties, canRead, canWrite) => {
        var path = PATH.join2(typeof parent == 'string' ? parent : FS.getPath(parent), name);
        var mode = FS.getMode(canRead, canWrite);
        return FS.create(path, mode);
      },createDataFile:(parent, name, data, canRead, canWrite, canOwn) => {
        var path = name;
        if (parent) {
          parent = typeof parent == 'string' ? parent : FS.getPath(parent);
          path = name ? PATH.join2(parent, name) : parent;
        }
        var mode = FS.getMode(canRead, canWrite);
        var node = FS.create(path, mode);
        if (data) {
          if (typeof data == 'string') {
            var arr = new Array(data.length);
            for (var i = 0, len = data.length; i < len; ++i) arr[i] = data.charCodeAt(i);
            data = arr;
          }
          // make sure we can write to the file
          FS.chmod(node, mode | 146);
          var stream = FS.open(node, 577);
          FS.write(stream, data, 0, data.length, 0, canOwn);
          FS.close(stream);
          FS.chmod(node, mode);
        }
        return node;
      },createDevice:(parent, name, input, output) => {
        var path = PATH.join2(typeof parent == 'string' ? parent : FS.getPath(parent), name);
        var mode = FS.getMode(!!input, !!output);
        if (!FS.createDevice.major) FS.createDevice.major = 64;
        var dev = FS.makedev(FS.createDevice.major++, 0);
        // Create a fake device that a set of stream ops to emulate
        // the old behavior.
        FS.registerDevice(dev, {
          open: (stream) => {
            stream.seekable = false;
          },
          close: (stream) => {
            // flush any pending line data
            if (output && output.buffer && output.buffer.length) {
              output(10);
            }
          },
          read: (stream, buffer, offset, length, pos /* ignored */) => {
            var bytesRead = 0;
            for (var i = 0; i < length; i++) {
              var result;
              try {
                result = input();
              } catch (e) {
                throw new FS.ErrnoError(29);
              }
              if (result === undefined && bytesRead === 0) {
                throw new FS.ErrnoError(6);
              }
              if (result === null || result === undefined) break;
              bytesRead++;
              buffer[offset+i] = result;
            }
            if (bytesRead) {
              stream.node.timestamp = Date.now();
            }
            return bytesRead;
          },
          write: (stream, buffer, offset, length, pos) => {
            for (var i = 0; i < length; i++) {
              try {
                output(buffer[offset+i]);
              } catch (e) {
                throw new FS.ErrnoError(29);
              }
            }
            if (length) {
              stream.node.timestamp = Date.now();
            }
            return i;
          }
        });
        return FS.mkdev(path, mode, dev);
      },forceLoadFile:(obj) => {
        if (obj.isDevice || obj.isFolder || obj.link || obj.contents) return true;
        if (typeof XMLHttpRequest != 'undefined') {
          throw new Error("Lazy loading should have been performed (contents set) in createLazyFile, but it was not. Lazy loading only works in web workers. Use --embed-file or --preload-file in emcc on the main thread.");
        } else if (read_) {
          // Command-line.
          try {
            // WARNING: Can't read binary files in V8's d8 or tracemonkey's js, as
            //          read() will try to parse UTF8.
            obj.contents = intArrayFromString(read_(obj.url), true);
            obj.usedBytes = obj.contents.length;
          } catch (e) {
            throw new FS.ErrnoError(29);
          }
        } else {
          throw new Error('Cannot load without read() or XMLHttpRequest.');
        }
      },createLazyFile:(parent, name, url, canRead, canWrite) => {
        // Lazy chunked Uint8Array (implements get and length from Uint8Array). Actual getting is abstracted away for eventual reuse.
        /** @constructor */
        function LazyUint8Array() {
          this.lengthKnown = false;
          this.chunks = []; // Loaded chunks. Index is the chunk number
        }
        LazyUint8Array.prototype.get = /** @this{Object} */ function LazyUint8Array_get(idx) {
          if (idx > this.length-1 || idx < 0) {
            return undefined;
          }
          var chunkOffset = idx % this.chunkSize;
          var chunkNum = (idx / this.chunkSize)|0;
          return this.getter(chunkNum)[chunkOffset];
        };
        LazyUint8Array.prototype.setDataGetter = function LazyUint8Array_setDataGetter(getter) {
          this.getter = getter;
        };
        LazyUint8Array.prototype.cacheLength = function LazyUint8Array_cacheLength() {
          // Find length
          var xhr = new XMLHttpRequest();
          xhr.open('HEAD', url, false);
          xhr.send(null);
          if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) throw new Error("Couldn't load " + url + ". Status: " + xhr.status);
          var datalength = Number(xhr.getResponseHeader("Content-length"));
          var header;
          var hasByteServing = (header = xhr.getResponseHeader("Accept-Ranges")) && header === "bytes";
          var usesGzip = (header = xhr.getResponseHeader("Content-Encoding")) && header === "gzip";
  
          var chunkSize = 1024*1024; // Chunk size in bytes
  
          if (!hasByteServing) chunkSize = datalength;
  
          // Function to get a range from the remote URL.
          var doXHR = (from, to) => {
            if (from > to) throw new Error("invalid range (" + from + ", " + to + ") or no bytes requested!");
            if (to > datalength-1) throw new Error("only " + datalength + " bytes available! programmer error!");
  
            // TODO: Use mozResponseArrayBuffer, responseStream, etc. if available.
            var xhr = new XMLHttpRequest();
            xhr.open('GET', url, false);
            if (datalength !== chunkSize) xhr.setRequestHeader("Range", "bytes=" + from + "-" + to);
  
            // Some hints to the browser that we want binary data.
            xhr.responseType = 'arraybuffer';
            if (xhr.overrideMimeType) {
              xhr.overrideMimeType('text/plain; charset=x-user-defined');
            }
  
            xhr.send(null);
            if (!(xhr.status >= 200 && xhr.status < 300 || xhr.status === 304)) throw new Error("Couldn't load " + url + ". Status: " + xhr.status);
            if (xhr.response !== undefined) {
              return new Uint8Array(/** @type{Array<number>} */(xhr.response || []));
            }
            return intArrayFromString(xhr.responseText || '', true);
          };
          var lazyArray = this;
          lazyArray.setDataGetter((chunkNum) => {
            var start = chunkNum * chunkSize;
            var end = (chunkNum+1) * chunkSize - 1; // including this byte
            end = Math.min(end, datalength-1); // if datalength-1 is selected, this is the last block
            if (typeof lazyArray.chunks[chunkNum] == 'undefined') {
              lazyArray.chunks[chunkNum] = doXHR(start, end);
            }
            if (typeof lazyArray.chunks[chunkNum] == 'undefined') throw new Error('doXHR failed!');
            return lazyArray.chunks[chunkNum];
          });
  
          if (usesGzip || !datalength) {
            // if the server uses gzip or doesn't supply the length, we have to download the whole file to get the (uncompressed) length
            chunkSize = datalength = 1; // this will force getter(0)/doXHR do download the whole file
            datalength = this.getter(0).length;
            chunkSize = datalength;
            out("LazyFiles on gzip forces download of the whole file when length is accessed");
          }
  
          this._length = datalength;
          this._chunkSize = chunkSize;
          this.lengthKnown = true;
        };
        if (typeof XMLHttpRequest != 'undefined') {
          if (!ENVIRONMENT_IS_WORKER) throw 'Cannot do synchronous binary XHRs outside webworkers in modern browsers. Use --embed-file or --preload-file in emcc';
          var lazyArray = new LazyUint8Array();
          Object.defineProperties(lazyArray, {
            length: {
              get: /** @this{Object} */ function() {
                if (!this.lengthKnown) {
                  this.cacheLength();
                }
                return this._length;
              }
            },
            chunkSize: {
              get: /** @this{Object} */ function() {
                if (!this.lengthKnown) {
                  this.cacheLength();
                }
                return this._chunkSize;
              }
            }
          });
  
          var properties = { isDevice: false, contents: lazyArray };
        } else {
          var properties = { isDevice: false, url: url };
        }
  
        var node = FS.createFile(parent, name, properties, canRead, canWrite);
        // This is a total hack, but I want to get this lazy file code out of the
        // core of MEMFS. If we want to keep this lazy file concept I feel it should
        // be its own thin LAZYFS proxying calls to MEMFS.
        if (properties.contents) {
          node.contents = properties.contents;
        } else if (properties.url) {
          node.contents = null;
          node.url = properties.url;
        }
        // Add a function that defers querying the file size until it is asked the first time.
        Object.defineProperties(node, {
          usedBytes: {
            get: /** @this {FSNode} */ function() { return this.contents.length; }
          }
        });
        // override each stream op with one that tries to force load the lazy file first
        var stream_ops = {};
        var keys = Object.keys(node.stream_ops);
        keys.forEach((key) => {
          var fn = node.stream_ops[key];
          stream_ops[key] = function forceLoadLazyFile() {
            FS.forceLoadFile(node);
            return fn.apply(null, arguments);
          };
        });
        function writeChunks(stream, buffer, offset, length, position) {
          var contents = stream.node.contents;
          if (position >= contents.length)
            return 0;
          var size = Math.min(contents.length - position, length);
          assert(size >= 0);
          if (contents.slice) { // normal array
            for (var i = 0; i < size; i++) {
              buffer[offset + i] = contents[position + i];
            }
          } else {
            for (var i = 0; i < size; i++) { // LazyUint8Array from sync binary XHR
              buffer[offset + i] = contents.get(position + i);
            }
          }
          return size;
        }
        // use a custom read function
        stream_ops.read = (stream, buffer, offset, length, position) => {
          FS.forceLoadFile(node);
          return writeChunks(stream, buffer, offset, length, position)
        };
        // use a custom mmap function
        stream_ops.mmap = (stream, length, position, prot, flags) => {
          FS.forceLoadFile(node);
          var ptr = mmapAlloc(length);
          if (!ptr) {
            throw new FS.ErrnoError(48);
          }
          writeChunks(stream, HEAP8, ptr, length, position);
          return { ptr: ptr, allocated: true };
        };
        node.stream_ops = stream_ops;
        return node;
      },createPreloadedFile:(parent, name, url, canRead, canWrite, onload, onerror, dontCreateFile, canOwn, preFinish) => {
        // TODO we should allow people to just pass in a complete filename instead
        // of parent and name being that we just join them anyways
        var fullname = name ? PATH_FS.resolve(PATH.join2(parent, name)) : parent;
        var dep = getUniqueRunDependency('cp ' + fullname); // might have several active requests for the same fullname
        function processData(byteArray) {
          function finish(byteArray) {
            if (preFinish) preFinish();
            if (!dontCreateFile) {
              FS.createDataFile(parent, name, byteArray, canRead, canWrite, canOwn);
            }
            if (onload) onload();
            removeRunDependency(dep);
          }
          if (Browser.handledByPreloadPlugin(byteArray, fullname, finish, () => {
            if (onerror) onerror();
            removeRunDependency(dep);
          })) {
            return;
          }
          finish(byteArray);
        }
        addRunDependency(dep);
        if (typeof url == 'string') {
          asyncLoad(url, (byteArray) => processData(byteArray), onerror);
        } else {
          processData(url);
        }
      },indexedDB:() => {
        return window.indexedDB || window.mozIndexedDB || window.webkitIndexedDB || window.msIndexedDB;
      },DB_NAME:() => {
        return 'EM_FS_' + window.location.pathname;
      },DB_VERSION:20,DB_STORE_NAME:"FILE_DATA",saveFilesToDB:(paths, onload = (() => {}), onerror = (() => {})) => {
        var indexedDB = FS.indexedDB();
        try {
          var openRequest = indexedDB.open(FS.DB_NAME(), FS.DB_VERSION);
        } catch (e) {
          return onerror(e);
        }
        openRequest.onupgradeneeded = () => {
          out('creating db');
          var db = openRequest.result;
          db.createObjectStore(FS.DB_STORE_NAME);
        };
        openRequest.onsuccess = () => {
          var db = openRequest.result;
          var transaction = db.transaction([FS.DB_STORE_NAME], 'readwrite');
          var files = transaction.objectStore(FS.DB_STORE_NAME);
          var ok = 0, fail = 0, total = paths.length;
          function finish() {
            if (fail == 0) onload(); else onerror();
          }
          paths.forEach((path) => {
            var putRequest = files.put(FS.analyzePath(path).object.contents, path);
            putRequest.onsuccess = () => { ok++; if (ok + fail == total) finish() };
            putRequest.onerror = () => { fail++; if (ok + fail == total) finish() };
          });
          transaction.onerror = onerror;
        };
        openRequest.onerror = onerror;
      },loadFilesFromDB:(paths, onload = (() => {}), onerror = (() => {})) => {
        var indexedDB = FS.indexedDB();
        try {
          var openRequest = indexedDB.open(FS.DB_NAME(), FS.DB_VERSION);
        } catch (e) {
          return onerror(e);
        }
        openRequest.onupgradeneeded = onerror; // no database to load from
        openRequest.onsuccess = () => {
          var db = openRequest.result;
          try {
            var transaction = db.transaction([FS.DB_STORE_NAME], 'readonly');
          } catch(e) {
            onerror(e);
            return;
          }
          var files = transaction.objectStore(FS.DB_STORE_NAME);
          var ok = 0, fail = 0, total = paths.length;
          function finish() {
            if (fail == 0) onload(); else onerror();
          }
          paths.forEach((path) => {
            var getRequest = files.get(path);
            getRequest.onsuccess = () => {
              if (FS.analyzePath(path).exists) {
                FS.unlink(path);
              }
              FS.createDataFile(PATH.dirname(path), PATH.basename(path), getRequest.result, true, true, true);
              ok++;
              if (ok + fail == total) finish();
            };
            getRequest.onerror = () => { fail++; if (ok + fail == total) finish() };
          });
          transaction.onerror = onerror;
        };
        openRequest.onerror = onerror;
      },absolutePath:() => {
        abort('FS.absolutePath has been removed; use PATH_FS.resolve instead');
      },createFolder:() => {
        abort('FS.createFolder has been removed; use FS.mkdir instead');
      },createLink:() => {
        abort('FS.createLink has been removed; use FS.symlink instead');
      },joinPath:() => {
        abort('FS.joinPath has been removed; use PATH.join instead');
      },mmapAlloc:() => {
        abort('FS.mmapAlloc has been replaced by the top level function mmapAlloc');
      },standardizePath:() => {
        abort('FS.standardizePath has been removed; use PATH.normalize instead');
      }};
  var SYSCALLS = {DEFAULT_POLLMASK:5,calculateAt:function(dirfd, path, allowEmpty) {
        if (PATH.isAbs(path)) {
          return path;
        }
        // relative path
        var dir;
        if (dirfd === -100) {
          dir = FS.cwd();
        } else {
          var dirstream = SYSCALLS.getStreamFromFD(dirfd);
          dir = dirstream.path;
        }
        if (path.length == 0) {
          if (!allowEmpty) {
            throw new FS.ErrnoError(44);;
          }
          return dir;
        }
        return PATH.join2(dir, path);
      },doStat:function(func, path, buf) {
        try {
          var stat = func(path);
        } catch (e) {
          if (e && e.node && PATH.normalize(path) !== PATH.normalize(FS.getPath(e.node))) {
            // an error occurred while trying to look up the path; we should just report ENOTDIR
            return -54;
          }
          throw e;
        }
        HEAP32[((buf)>>2)] = stat.dev;
        HEAP32[(((buf)+(8))>>2)] = stat.ino;
        HEAP32[(((buf)+(12))>>2)] = stat.mode;
        HEAPU32[(((buf)+(16))>>2)] = stat.nlink;
        HEAP32[(((buf)+(20))>>2)] = stat.uid;
        HEAP32[(((buf)+(24))>>2)] = stat.gid;
        HEAP32[(((buf)+(28))>>2)] = stat.rdev;
        (tempI64 = [stat.size>>>0,(tempDouble=stat.size,(+(Math.abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math.min((+(Math.floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math.ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[(((buf)+(40))>>2)] = tempI64[0],HEAP32[(((buf)+(44))>>2)] = tempI64[1]);
        HEAP32[(((buf)+(48))>>2)] = 4096;
        HEAP32[(((buf)+(52))>>2)] = stat.blocks;
        var atime = stat.atime.getTime();
        var mtime = stat.mtime.getTime();
        var ctime = stat.ctime.getTime();
        (tempI64 = [Math.floor(atime / 1000)>>>0,(tempDouble=Math.floor(atime / 1000),(+(Math.abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math.min((+(Math.floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math.ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[(((buf)+(56))>>2)] = tempI64[0],HEAP32[(((buf)+(60))>>2)] = tempI64[1]);
        HEAPU32[(((buf)+(64))>>2)] = (atime % 1000) * 1000;
        (tempI64 = [Math.floor(mtime / 1000)>>>0,(tempDouble=Math.floor(mtime / 1000),(+(Math.abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math.min((+(Math.floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math.ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[(((buf)+(72))>>2)] = tempI64[0],HEAP32[(((buf)+(76))>>2)] = tempI64[1]);
        HEAPU32[(((buf)+(80))>>2)] = (mtime % 1000) * 1000;
        (tempI64 = [Math.floor(ctime / 1000)>>>0,(tempDouble=Math.floor(ctime / 1000),(+(Math.abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math.min((+(Math.floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math.ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[(((buf)+(88))>>2)] = tempI64[0],HEAP32[(((buf)+(92))>>2)] = tempI64[1]);
        HEAPU32[(((buf)+(96))>>2)] = (ctime % 1000) * 1000;
        (tempI64 = [stat.ino>>>0,(tempDouble=stat.ino,(+(Math.abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math.min((+(Math.floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math.ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[(((buf)+(104))>>2)] = tempI64[0],HEAP32[(((buf)+(108))>>2)] = tempI64[1]);
        return 0;
      },doMsync:function(addr, stream, len, flags, offset) {
        if (!FS.isFile(stream.node.mode)) {
          throw new FS.ErrnoError(43);
        }
        if (flags & 2) {
          // MAP_PRIVATE calls need not to be synced back to underlying fs
          return 0;
        }
        var buffer = HEAPU8.slice(addr, addr + len);
        FS.msync(stream, buffer, offset, len, flags);
      },varargs:undefined,get:function() {
        assert(SYSCALLS.varargs != undefined);
        SYSCALLS.varargs += 4;
        var ret = HEAP32[(((SYSCALLS.varargs)-(4))>>2)];
        return ret;
      },getStr:function(ptr) {
        var ret = UTF8ToString(ptr);
        return ret;
      },getStreamFromFD:function(fd) {
        var stream = FS.getStream(fd);
        if (!stream) throw new FS.ErrnoError(8);
        return stream;
      }};
  
  function _proc_exit(code) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(1, 1, code);
  
      EXITSTATUS = code;
      if (!keepRuntimeAlive()) {
        PThread.terminateAllThreads();
        if (Module['onExit']) Module['onExit'](code);
        ABORT = true;
      }
      quit_(code, new ExitStatus(code));
    
  }
  
  /** @param {boolean|number=} implicit */
  function exitJS(status, implicit) {
      EXITSTATUS = status;
  
      checkUnflushedContent();
  
      if (ENVIRONMENT_IS_PTHREAD) {
        // implict exit can never happen on a pthread
        assert(!implicit);
        // When running in a pthread we propagate the exit back to the main thread
        // where it can decide if the whole process should be shut down or not.
        // The pthread may have decided not to exit its own runtime, for example
        // because it runs a main loop, but that doesn't affect the main thread.
        exitOnMainThread(status);
        throw 'unwind';
      }
  
      // if exit() was called explicitly, warn the user if the runtime isn't actually being shut down
      if (keepRuntimeAlive() && !implicit) {
        var msg = 'program exited (with status: ' + status + '), but EXIT_RUNTIME is not set, so halting execution but not exiting the runtime or preventing further async execution (build with EXIT_RUNTIME=1, if you want a true shutdown)';
        readyPromiseReject(msg);
        err(msg);
      }
  
      _proc_exit(status);
    }
  var _exit = exitJS;
  
  function ptrToString(ptr) {
      assert(typeof ptr === 'number');
      return '0x' + ptr.toString(16).padStart(8, '0');
    }
  
  function handleException(e) {
      // Certain exception types we do not treat as errors since they are used for
      // internal control flow.
      // 1. ExitStatus, which is thrown by exit()
      // 2. "unwind", which is thrown by emscripten_unwind_to_js_event_loop() and others
      //    that wish to return to JS event loop.
      if (e instanceof ExitStatus || e == 'unwind') {
        return EXITSTATUS;
      }
      checkStackCookie();
      if (e instanceof WebAssembly.RuntimeError) {
        if (_emscripten_stack_get_current() <= 0) {
          err('Stack overflow detected.  You can try increasing -sSTACK_SIZE (currently set to ' + 65536 + ')');
        }
      }
      quit_(1, e);
    }
  
  var PThread = {unusedWorkers:[],runningWorkers:[],tlsInitFunctions:[],pthreads:{},nextWorkerID:1,debugInit:function() {
        function pthreadLogPrefix() {
          var t = 0;
          if (runtimeInitialized && typeof _pthread_self != 'undefined'
          ) {
            t = _pthread_self();
          }
          return 'w:' + (Module['workerID'] || 0) + ',t:' + ptrToString(t) + ': ';
        }
  
        // Prefix all err()/dbg() messages with the calling thread ID.
        var origDbg = dbg;
        dbg = (message) => origDbg(pthreadLogPrefix() + message);
      },init:function() {
        PThread.debugInit();
        if (ENVIRONMENT_IS_PTHREAD
          ) {
          PThread.initWorker();
        } else {
          PThread.initMainThread();
        }
      },initMainThread:function() {
      },initWorker:function() {
  
        // The default behaviour for pthreads is always to exit once they return
        // from their entry point (or call pthread_exit).  If we set noExitRuntime
        // to true here on pthreads they would never complete and attempt to
        // pthread_join to them would block forever.
        // pthreads can still choose to set `noExitRuntime` explicitly, or
        // call emscripten_unwind_to_js_event_loop to extend their lifetime beyond
        // their main function.  See comment in src/worker.js for more.
        noExitRuntime = false;
      },setExitStatus:function(status) {
        EXITSTATUS = status;
      },terminateAllThreads__deps:["$terminateWorker"],terminateAllThreads:function() {
        assert(!ENVIRONMENT_IS_PTHREAD, 'Internal Error! terminateAllThreads() can only ever be called from main application thread!');
        // Attempt to kill all workers.  Sadly (at least on the web) there is no
        // way to terminate a worker synchronously, or to be notified when a
        // worker in actually terminated.  This means there is some risk that
        // pthreads will continue to be executing after `worker.terminate` has
        // returned.  For this reason, we don't call `returnWorkerToPool` here or
        // free the underlying pthread data structures.
        for (var worker of PThread.runningWorkers) {
          terminateWorker(worker);
        }
        for (var worker of PThread.unusedWorkers) {
          terminateWorker(worker);
        }
        PThread.unusedWorkers = [];
        PThread.runningWorkers = [];
        PThread.pthreads = [];
      },returnWorkerToPool:function(worker) {
        // We don't want to run main thread queued calls here, since we are doing
        // some operations that leave the worker queue in an invalid state until
        // we are completely done (it would be bad if free() ends up calling a
        // queued pthread_create which looks at the global data structures we are
        // modifying). To achieve that, defer the free() til the very end, when
        // we are all done.
        var pthread_ptr = worker.pthread_ptr;
        delete PThread.pthreads[pthread_ptr];
        // Note: worker is intentionally not terminated so the pool can
        // dynamically grow.
        PThread.unusedWorkers.push(worker);
        PThread.runningWorkers.splice(PThread.runningWorkers.indexOf(worker), 1);
        // Not a running Worker anymore
        // Detach the worker from the pthread object, and return it to the
        // worker pool as an unused worker.
        worker.pthread_ptr = 0;
  
        if (ENVIRONMENT_IS_NODE) {
          // Once a pthread has finished and the worker becomes idle, mark it
          // as weakly referenced so that its existence does not prevent Node.js
          // from exiting.
          worker.unref();
        }
  
        // Finally, free the underlying (and now-unused) pthread structure in
        // linear memory.
        __emscripten_thread_free_data(pthread_ptr);
      },receiveObjectTransfer:function(data) {
      },threadInitTLS:function() {
        // Call thread init functions (these are the _emscripten_tls_init for each
        // module loaded.
        PThread.tlsInitFunctions.forEach((f) => f());
      },loadWasmModuleToWorker:(worker) => new Promise((onFinishedLoading) => {
        worker.onmessage = (e) => {
          var d = e['data'];
          var cmd = d['cmd'];
          // Sometimes we need to backproxy events to the calling thread (e.g.
          // HTML5 DOM events handlers such as
          // emscripten_set_mousemove_callback()), so keep track in a globally
          // accessible variable about the thread that initiated the proxying.
          if (worker.pthread_ptr) PThread.currentProxiedOperationCallerThread = worker.pthread_ptr;
  
          // If this message is intended to a recipient that is not the main thread, forward it to the target thread.
          if (d['targetThread'] && d['targetThread'] != _pthread_self()) {
            var targetWorker = PThread.pthreads[d.targetThread];
            if (targetWorker) {
              targetWorker.postMessage(d, d['transferList']);
            } else {
              err('Internal error! Worker sent a message "' + cmd + '" to target pthread ' + d['targetThread'] + ', but that thread no longer exists!');
            }
            PThread.currentProxiedOperationCallerThread = undefined;
            return;
          }
  
          if (cmd === 'processProxyingQueue') {
            executeNotifiedProxyingQueue(d['queue']);
          } else if (cmd === 'spawnThread') {
            spawnThread(d);
          } else if (cmd === 'cleanupThread') {
            cleanupThread(d['thread']);
          } else if (cmd === 'killThread') {
            killThread(d['thread']);
          } else if (cmd === 'cancelThread') {
            cancelThread(d['thread']);
          } else if (cmd === 'loaded') {
            worker.loaded = true;
            // Check that this worker doesn't have an associated pthread.
            if (ENVIRONMENT_IS_NODE && !worker.pthread_ptr) {
              // Once worker is loaded & idle, mark it as weakly referenced,
              // so that mere existence of a Worker in the pool does not prevent
              // Node.js from exiting the app.
              worker.unref();
            }
            onFinishedLoading(worker);
          } else if (cmd === 'print') {
            out('Thread ' + d['threadId'] + ': ' + d['text']);
          } else if (cmd === 'printErr') {
            err('Thread ' + d['threadId'] + ': ' + d['text']);
          } else if (cmd === 'alert') {
            alert('Thread ' + d['threadId'] + ': ' + d['text']);
          } else if (d.target === 'setimmediate') {
            // Worker wants to postMessage() to itself to implement setImmediate()
            // emulation.
            worker.postMessage(d);
          } else if (cmd === 'callHandler') {
            Module[d['handler']](...d['args']);
          } else if (cmd) {
            // The received message looks like something that should be handled by this message
            // handler, (since there is a e.data.cmd field present), but is not one of the
            // recognized commands:
            err("worker sent an unknown command " + cmd);
          }
          PThread.currentProxiedOperationCallerThread = undefined;
        };
  
        worker.onerror = (e) => {
          var message = 'worker sent an error!';
          if (worker.pthread_ptr) {
            message = 'Pthread ' + ptrToString(worker.pthread_ptr) + ' sent an error!';
          }
          err(message + ' ' + e.filename + ':' + e.lineno + ': ' + e.message);
          throw e;
        };
  
        if (ENVIRONMENT_IS_NODE) {
          worker.on('message', function(data) {
            worker.onmessage({ data: data });
          });
          worker.on('error', function(e) {
            worker.onerror(e);
          });
          worker.on('detachedExit', function() {
            // TODO: update the worker queue?
            // See: https://github.com/emscripten-core/emscripten/issues/9763
          });
        }
  
        assert(wasmMemory instanceof WebAssembly.Memory, 'WebAssembly memory should have been loaded by now!');
        assert(wasmModule instanceof WebAssembly.Module, 'WebAssembly Module should have been loaded by now!');
  
        // When running on a pthread, none of the incoming parameters on the module
        // object are present. Proxy known handlers back to the main thread if specified.
        var handlers = [];
        var knownHandlers = [
          'onExit',
          'onAbort',
          'print',
          'printErr',
        ];
        for (var handler of knownHandlers) {
          if (Module.hasOwnProperty(handler)) {
            handlers.push(handler);
          }
        }
  
        worker.workerID = PThread.nextWorkerID++;
  
        // Ask the new worker to load up the Emscripten-compiled page. This is a heavy operation.
        worker.postMessage({
          'cmd': 'load',
          'handlers': handlers,
          // If the application main .js file was loaded from a Blob, then it is not possible
          // to access the URL of the current script that could be passed to a Web Worker so that
          // it could load up the same file. In that case, developer must either deliver the Blob
          // object in Module['mainScriptUrlOrBlob'], or a URL to it, so that pthread Workers can
          // independently load up the same main application file.
          'urlOrBlob': Module['mainScriptUrlOrBlob']
          || _scriptDir
          ,
          'wasmMemory': wasmMemory,
          'wasmModule': wasmModule,
          'workerID': worker.workerID,
        });
      }),loadWasmModuleToAllWorkers:function(onMaybeReady) {
        onMaybeReady();
      },allocateUnusedWorker:function() {
        var worker;
        // Allow HTML module to configure the location where the 'worker.js' file will be loaded from,
        // via Module.locateFile() function. If not specified, then the default URL 'worker.js' relative
        // to the main html file is loaded.
        var pthreadMainJs = locateFile('z3-built.worker.js');
        worker = new Worker(pthreadMainJs);
      PThread.unusedWorkers.push(worker);
      },getNewWorker:function() {
        if (PThread.unusedWorkers.length == 0) {
  // PTHREAD_POOL_SIZE_STRICT should show a warning and, if set to level `2`, return from the function.
          PThread.allocateUnusedWorker();
          PThread.loadWasmModuleToWorker(PThread.unusedWorkers[0]);
        }
        return PThread.unusedWorkers.pop();
      }};
  Module["PThread"] = PThread;

  function callRuntimeCallbacks(callbacks) {
      while (callbacks.length > 0) {
        // Pass the module as the first argument.
        callbacks.shift()(Module);
      }
    }

  
  var wasmTableMirror = [];
  
  function getWasmTableEntry(funcPtr) {
      var func = wasmTableMirror[funcPtr];
      if (!func) {
        if (funcPtr >= wasmTableMirror.length) wasmTableMirror.length = funcPtr + 1;
        wasmTableMirror[funcPtr] = func = wasmTable.get(funcPtr);
      }
      assert(wasmTable.get(funcPtr) == func, "JavaScript-side Wasm function table mirror is out of date!");
      return func;
    }
  function exception_decRef(info) {
      // A rethrown exception can reach refcount 0; it must not be discarded
      // Its next handler will clear the rethrown flag and addRef it, prior to
      // final decRef and destruction here
      if (info.release_ref() && !info.get_rethrown()) {
        var destructor = info.get_destructor();
        if (destructor) {
          // In Wasm, destructors return 'this' as in ARM
          getWasmTableEntry(destructor)(info.excPtr);
        }
        ___cxa_free_exception(info.excPtr);
      }
    }
  
  /** @constructor */
  function ExceptionInfo(excPtr) {
      this.excPtr = excPtr;
      this.ptr = excPtr - 24;
  
      this.set_type = function(type) {
        HEAPU32[(((this.ptr)+(4))>>2)] = type;
      };
  
      this.get_type = function() {
        return HEAPU32[(((this.ptr)+(4))>>2)];
      };
  
      this.set_destructor = function(destructor) {
        HEAPU32[(((this.ptr)+(8))>>2)] = destructor;
      };
  
      this.get_destructor = function() {
        return HEAPU32[(((this.ptr)+(8))>>2)];
      };
  
      this.set_refcount = function(refcount) {
        HEAP32[((this.ptr)>>2)] = refcount;
      };
  
      this.set_caught = function (caught) {
        caught = caught ? 1 : 0;
        HEAP8[(((this.ptr)+(12))>>0)] = caught;
      };
  
      this.get_caught = function () {
        return HEAP8[(((this.ptr)+(12))>>0)] != 0;
      };
  
      this.set_rethrown = function (rethrown) {
        rethrown = rethrown ? 1 : 0;
        HEAP8[(((this.ptr)+(13))>>0)] = rethrown;
      };
  
      this.get_rethrown = function () {
        return HEAP8[(((this.ptr)+(13))>>0)] != 0;
      };
  
      // Initialize native structure fields. Should be called once after allocated.
      this.init = function(type, destructor) {
        this.set_adjusted_ptr(0);
        this.set_type(type);
        this.set_destructor(destructor);
        this.set_refcount(0);
        this.set_caught(false);
        this.set_rethrown(false);
      }
  
      this.add_ref = function() {
        Atomics.add(HEAP32, (this.ptr + 0) >> 2, 1);
      };
  
      // Returns true if last reference released.
      this.release_ref = function() {
        var prev = Atomics.sub(HEAP32, (this.ptr + 0) >> 2, 1);
        assert(prev > 0);
        return prev === 1;
      };
  
      this.set_adjusted_ptr = function(adjustedPtr) {
        HEAPU32[(((this.ptr)+(16))>>2)] = adjustedPtr;
      };
  
      this.get_adjusted_ptr = function() {
        return HEAPU32[(((this.ptr)+(16))>>2)];
      };
  
      // Get pointer which is expected to be received by catch clause in C++ code. It may be adjusted
      // when the pointer is casted to some of the exception object base classes (e.g. when virtual
      // inheritance is used). When a pointer is thrown this method should return the thrown pointer
      // itself.
      this.get_exception_ptr = function() {
        // Work around a fastcomp bug, this code is still included for some reason in a build without
        // exceptions support.
        var isPointer = ___cxa_is_pointer_type(this.get_type());
        if (isPointer) {
          return HEAPU32[((this.excPtr)>>2)];
        }
        var adjusted = this.get_adjusted_ptr();
        if (adjusted !== 0) return adjusted;
        return this.excPtr;
      };
    }
  function ___cxa_decrement_exception_refcount(ptr) {
      if (!ptr) return;
      exception_decRef(new ExceptionInfo(ptr));
    }
  function decrementExceptionRefcount(ptr) {
      ___cxa_decrement_exception_refcount(ptr);
    }


  function establishStackSpace() {
      var pthread_ptr = _pthread_self();
      var stackTop = HEAP32[(((pthread_ptr)+(52))>>2)];
      var stackSize = HEAP32[(((pthread_ptr)+(56))>>2)];
      var stackMax = stackTop - stackSize;
      assert(stackTop != 0);
      assert(stackMax != 0);
      assert(stackTop > stackMax, 'stackTop must be higher then stackMax');
      // Set stack limits used by `emscripten/stack.h` function.  These limits are
      // cached in wasm-side globals to make checks as fast as possible.
      _emscripten_stack_set_limits(stackTop, stackMax);
  
      // Call inside wasm module to set up the stack frame for this pthread in wasm module scope
      stackRestore(stackTop);
  
      // Write the stack cookie last, after we have set up the proper bounds and
      // current position of the stack.
      writeStackCookie();
    }
  Module["establishStackSpace"] = establishStackSpace;

  
  
  
  function exitOnMainThread(returnCode) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(2, 0, returnCode);
  
      try {
        _exit(returnCode);
      } catch (e) {
        handleException(e);
      }
    
  }
  

  
  
  function getExceptionMessageCommon(ptr) {
      return withStackSave(function() {
        var type_addr_addr = stackAlloc(4);
        var message_addr_addr = stackAlloc(4);
        ___get_exception_message(ptr, type_addr_addr, message_addr_addr);
        var type_addr = HEAPU32[((type_addr_addr)>>2)];
        var message_addr = HEAPU32[((message_addr_addr)>>2)];
        var type = UTF8ToString(type_addr);
        _free(type_addr);
        var message;
        if (message_addr) {
          message = UTF8ToString(message_addr);
          _free(message_addr);
        }
        return [type, message];
      });
    }
  function getExceptionMessage(ptr) {
      return getExceptionMessageCommon(ptr);
    }
  Module["getExceptionMessage"] = getExceptionMessage;

  
    /**
     * @param {number} ptr
     * @param {string} type
     */
  function getValue(ptr, type = 'i8') {
    if (type.endsWith('*')) type = '*';
    switch (type) {
      case 'i1': return HEAP8[((ptr)>>0)];
      case 'i8': return HEAP8[((ptr)>>0)];
      case 'i16': return HEAP16[((ptr)>>1)];
      case 'i32': return HEAP32[((ptr)>>2)];
      case 'i64': return HEAP64[((ptr)>>3)];
      case 'float': return HEAPF32[((ptr)>>2)];
      case 'double': return HEAPF64[((ptr)>>3)];
      case '*': return HEAPU32[((ptr)>>2)];
      default: abort('invalid type for getValue: ' + type);
    }
  }

  function exception_addRef(info) {
      info.add_ref();
    }
  
  function ___cxa_increment_exception_refcount(ptr) {
      if (!ptr) return;
      exception_addRef(new ExceptionInfo(ptr));
    }
  function incrementExceptionRefcount(ptr) {
      ___cxa_increment_exception_refcount(ptr);
    }

  
  
  function invokeEntryPoint(ptr, arg) {
      // pthread entry points are always of signature 'void *ThreadMain(void *arg)'
      // Native codebases sometimes spawn threads with other thread entry point
      // signatures, such as void ThreadMain(void *arg), void *ThreadMain(), or
      // void ThreadMain().  That is not acceptable per C/C++ specification, but
      // x86 compiler ABI extensions enable that to work. If you find the
      // following line to crash, either change the signature to "proper" void
      // *ThreadMain(void *arg) form, or try linking with the Emscripten linker
      // flag -sEMULATE_FUNCTION_POINTER_CASTS to add in emulation for this x86
      // ABI extension.
      var result = getWasmTableEntry(ptr)(arg);
      checkStackCookie();
      if (keepRuntimeAlive()) {
        PThread.setExitStatus(result);
      } else {
        __emscripten_thread_exit(result);
      }
    }
  Module["invokeEntryPoint"] = invokeEntryPoint;


  function registerTLSInit(tlsInitFunc) {
      PThread.tlsInitFunctions.push(tlsInitFunc);
    }

  
    /**
     * @param {number} ptr
     * @param {number} value
     * @param {string} type
     */
  function setValue(ptr, value, type = 'i8') {
    if (type.endsWith('*')) type = '*';
    switch (type) {
      case 'i1': HEAP8[((ptr)>>0)] = value; break;
      case 'i8': HEAP8[((ptr)>>0)] = value; break;
      case 'i16': HEAP16[((ptr)>>1)] = value; break;
      case 'i32': HEAP32[((ptr)>>2)] = value; break;
      case 'i64': (tempI64 = [value>>>0,(tempDouble=value,(+(Math.abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math.min((+(Math.floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math.ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[((ptr)>>2)] = tempI64[0],HEAP32[(((ptr)+(4))>>2)] = tempI64[1]); break;
      case 'float': HEAPF32[((ptr)>>2)] = value; break;
      case 'double': HEAPF64[((ptr)>>3)] = value; break;
      case '*': HEAPU32[((ptr)>>2)] = value; break;
      default: abort('invalid type for setValue: ' + type);
    }
  }

  function jsStackTrace() {
      var error = new Error();
      if (!error.stack) {
        // IE10+ special cases: It does have callstack info, but it is only
        // populated if an Error object is thrown, so try that as a special-case.
        try {
          throw new Error();
        } catch(e) {
          error = e;
        }
        if (!error.stack) {
          return '(no stack trace available)';
        }
      }
      return error.stack.toString();
    }
  
  function stackTrace() {
      var js = jsStackTrace();
      if (Module['extraStackTrace']) js += '\n' + Module['extraStackTrace']();
      return demangleAll(js);
    }

  function warnOnce(text) {
      if (!warnOnce.shown) warnOnce.shown = {};
      if (!warnOnce.shown[text]) {
        warnOnce.shown[text] = 1;
        if (ENVIRONMENT_IS_NODE) text = 'warning: ' + text;
        err(text);
      }
    }

  function ___assert_fail(condition, filename, line, func) {
      abort('Assertion failed: ' + UTF8ToString(condition) + ', at: ' + [filename ? UTF8ToString(filename) : 'unknown filename', line, func ? UTF8ToString(func) : 'unknown function']);
    }

  function ___call_sighandler(fp, sig) {
      getWasmTableEntry(fp)(sig);
    }

  var exceptionCaught =  [];
  
  
  var uncaughtExceptionCount = 0;
  function ___cxa_begin_catch(ptr) {
      var info = new ExceptionInfo(ptr);
      if (!info.get_caught()) {
        info.set_caught(true);
        uncaughtExceptionCount--;
      }
      info.set_rethrown(false);
      exceptionCaught.push(info);
      exception_addRef(info);
      return info.get_exception_ptr();
    }

  
  var exceptionLast = 0;
  
  function ___cxa_end_catch() {
      // Clear state flag.
      _setThrew(0);
      assert(exceptionCaught.length > 0);
      // Call destructor if one is registered then clear it.
      var info = exceptionCaught.pop();
  
      exception_decRef(info);
      exceptionLast = 0; // XXX in decRef?
    }

  
  
  function ___resumeException(ptr) {
      if (!exceptionLast) { exceptionLast = ptr; }
      throw new CppException(ptr);
    }
  
  
  function ___cxa_find_matching_catch() {
      var thrown = exceptionLast;
      if (!thrown) {
        // just pass through the null ptr
        setTempRet0(0);
        return 0;
      }
      var info = new ExceptionInfo(thrown);
      info.set_adjusted_ptr(thrown);
      var thrownType = info.get_type();
      if (!thrownType) {
        // just pass through the thrown ptr
        setTempRet0(0);
        return thrown;
      }
  
      // can_catch receives a **, add indirection
      // The different catch blocks are denoted by different types.
      // Due to inheritance, those types may not precisely match the
      // type of the thrown object. Find one which matches, and
      // return the type of the catch block which should be called.
      for (var i = 0; i < arguments.length; i++) {
        var caughtType = arguments[i];
        if (caughtType === 0 || caughtType === thrownType) {
          // Catch all clause matched or exactly the same type is caught
          break;
        }
        var adjusted_ptr_addr = info.ptr + 16;
        if (___cxa_can_catch(caughtType, thrownType, adjusted_ptr_addr)) {
          setTempRet0(caughtType);
          return thrown;
        }
      }
      setTempRet0(thrownType);
      return thrown;
    }
  var ___cxa_find_matching_catch_2 = ___cxa_find_matching_catch;

  var ___cxa_find_matching_catch_3 = ___cxa_find_matching_catch;

  var ___cxa_find_matching_catch_4 = ___cxa_find_matching_catch;

  var ___cxa_find_matching_catch_7 = ___cxa_find_matching_catch;

  var ___cxa_find_matching_catch_8 = ___cxa_find_matching_catch;

  
  
  function ___cxa_rethrow() {
      var info = exceptionCaught.pop();
      if (!info) {
        abort('no exception to throw');
      }
      var ptr = info.excPtr;
      if (!info.get_rethrown()) {
        // Only pop if the corresponding push was through rethrow_primary_exception
        exceptionCaught.push(info);
        info.set_rethrown(true);
        info.set_caught(false);
        uncaughtExceptionCount++;
      }
      exceptionLast = ptr;
      throw new CppException(ptr);
    }

  
  
  function ___cxa_throw(ptr, type, destructor) {
      var info = new ExceptionInfo(ptr);
      // Initialize ExceptionInfo content after it was allocated in __cxa_allocate_exception.
      info.init(type, destructor);
      exceptionLast = ptr;
      uncaughtExceptionCount++;
      throw new CppException(ptr);
    }

  function ___cxa_uncaught_exceptions() {
      return uncaughtExceptionCount;
    }

  function ___emscripten_init_main_thread_js(tb) {
      // Pass the thread address to the native code where they stored in wasm
      // globals which act as a form of TLS. Global constructors trying
      // to access this value will read the wrong value, but that is UB anyway.
      __emscripten_thread_init(
        tb,
        /*isMainBrowserThread=*/!ENVIRONMENT_IS_WORKER,
        /*isMainRuntimeThread=*/1,
        /*canBlock=*/!ENVIRONMENT_IS_WEB,
      );
      PThread.threadInitTLS();
    }

  function ___emscripten_thread_cleanup(thread) {
      // Called when a thread needs to be cleaned up so it can be reused.
      // A thread is considered reusable when it either returns from its
      // entry point, calls pthread_exit, or acts upon a cancellation.
      // Detached threads are responsible for calling this themselves,
      // otherwise pthread_join is responsible for calling this.
      if (!ENVIRONMENT_IS_PTHREAD) cleanupThread(thread);
      else postMessage({ 'cmd': 'cleanupThread', 'thread': thread });
    }

  
  
  
  
  function pthreadCreateProxied(pthread_ptr, attr, startRoutine, arg) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(3, 1, pthread_ptr, attr, startRoutine, arg);
  
      return ___pthread_create_js(pthread_ptr, attr, startRoutine, arg);
    
  }
  
  
  function ___pthread_create_js(pthread_ptr, attr, startRoutine, arg) {
      if (typeof SharedArrayBuffer == 'undefined') {
        err('Current environment does not support SharedArrayBuffer, pthreads are not available!');
        return 6;
      }
  
      // List of JS objects that will transfer ownership to the Worker hosting the thread
      var transferList = [];
      var error = 0;
  
      // Synchronously proxy the thread creation to main thread if possible. If we
      // need to transfer ownership of objects, then proxy asynchronously via
      // postMessage.
      if (ENVIRONMENT_IS_PTHREAD && (transferList.length === 0 || error)) {
        return pthreadCreateProxied(pthread_ptr, attr, startRoutine, arg);
      }
  
      // If on the main thread, and accessing Canvas/OffscreenCanvas failed, abort
      // with the detected error.
      if (error) return error;
  
      var threadParams = {
        startRoutine,
        pthread_ptr,
        arg,
        transferList,
      };
  
      if (ENVIRONMENT_IS_PTHREAD) {
        // The prepopulated pool of web workers that can host pthreads is stored
        // in the main JS thread. Therefore if a pthread is attempting to spawn a
        // new thread, the thread creation must be deferred to the main JS thread.
        threadParams.cmd = 'spawnThread';
        postMessage(threadParams, transferList);
        // When we defer thread creation this way, we have no way to detect thread
        // creation synchronously today, so we have to assume success and return 0.
        return 0;
      }
  
      // We are the main thread, so we have the pthread warmup pool in this
      // thread and can fire off JS thread creation directly ourselves.
      return spawnThread(threadParams);
    }


  function setErrNo(value) {
      HEAP32[((___errno_location())>>2)] = value;
      return value;
    }
  
  
  function ___syscall_fcntl64(fd, cmd, varargs) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(4, 1, fd, cmd, varargs);
  
  SYSCALLS.varargs = varargs;
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      switch (cmd) {
        case 0: {
          var arg = SYSCALLS.get();
          if (arg < 0) {
            return -28;
          }
          var newStream;
          newStream = FS.createStream(stream, arg);
          return newStream.fd;
        }
        case 1:
        case 2:
          return 0;  // FD_CLOEXEC makes no sense for a single process.
        case 3:
          return stream.flags;
        case 4: {
          var arg = SYSCALLS.get();
          stream.flags |= arg;
          return 0;
        }
        case 5:
        /* case 5: Currently in musl F_GETLK64 has same value as F_GETLK, so omitted to avoid duplicate case blocks. If that changes, uncomment this */ {
          
          var arg = SYSCALLS.get();
          var offset = 0;
          // We're always unlocked.
          HEAP16[(((arg)+(offset))>>1)] = 2;
          return 0;
        }
        case 6:
        case 7:
        /* case 6: Currently in musl F_SETLK64 has same value as F_SETLK, so omitted to avoid duplicate case blocks. If that changes, uncomment this */
        /* case 7: Currently in musl F_SETLKW64 has same value as F_SETLKW, so omitted to avoid duplicate case blocks. If that changes, uncomment this */
          
          
          return 0; // Pretend that the locking is successful.
        case 16:
        case 8:
          return -28; // These are for sockets. We don't have them fully implemented yet.
        case 9:
          // musl trusts getown return values, due to a bug where they must be, as they overlap with errors. just return -1 here, so fcntl() returns that, and we set errno ourselves.
          setErrNo(28);
          return -1;
        default: {
          return -28;
        }
      }
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  
  }
  

  
  function ___syscall_ioctl(fd, op, varargs) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(5, 1, fd, op, varargs);
  
  SYSCALLS.varargs = varargs;
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      switch (op) {
        case 21509:
        case 21505: {
          if (!stream.tty) return -59;
          return 0;
        }
        case 21510:
        case 21511:
        case 21512:
        case 21506:
        case 21507:
        case 21508: {
          if (!stream.tty) return -59;
          return 0; // no-op, not actually adjusting terminal settings
        }
        case 21519: {
          if (!stream.tty) return -59;
          var argp = SYSCALLS.get();
          HEAP32[((argp)>>2)] = 0;
          return 0;
        }
        case 21520: {
          if (!stream.tty) return -59;
          return -28; // not supported
        }
        case 21531: {
          var argp = SYSCALLS.get();
          return FS.ioctl(stream, op, argp);
        }
        case 21523: {
          // TODO: in theory we should write to the winsize struct that gets
          // passed in, but for now musl doesn't read anything on it
          if (!stream.tty) return -59;
          return 0;
        }
        case 21524: {
          // TODO: technically, this ioctl call should change the window size.
          // but, since emscripten doesn't have any concept of a terminal window
          // yet, we'll just silently throw it away as we do TIOCGWINSZ
          if (!stream.tty) return -59;
          return 0;
        }
        default: return -28; // not supported
      }
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  
  }
  

  
  function ___syscall_openat(dirfd, path, flags, varargs) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(6, 1, dirfd, path, flags, varargs);
  
  SYSCALLS.varargs = varargs;
  try {
  
      path = SYSCALLS.getStr(path);
      path = SYSCALLS.calculateAt(dirfd, path);
      var mode = varargs ? SYSCALLS.get() : 0;
      return FS.open(path, flags, mode).fd;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return -e.errno;
  }
  
  }
  

  function __emscripten_default_pthread_stack_size() {
      return 65536;
    }

  var nowIsMonotonic = true;;
  function __emscripten_get_now_is_monotonic() {
      return nowIsMonotonic;
    }

  function executeNotifiedProxyingQueue(queue) {
      // Set the notification state to processing.
      Atomics.store(HEAP32, queue >> 2, 1);
      // Only execute the queue if we have a live pthread runtime. We
      // implement pthread_self to return 0 if there is no live runtime.
      // TODO: Use `callUserCallback` to correctly handle unwinds, etc. once
      //       `runtimeExited` is correctly unset on workers.
      if (_pthread_self()) {
        __emscripten_proxy_execute_task_queue(queue);
      }
      // Set the notification state to none as long as a new notification has not
      // been sent while we were processing.
      Atomics.compareExchange(HEAP32, queue >> 2,
                              1,
                              0);
    }
  Module["executeNotifiedProxyingQueue"] = executeNotifiedProxyingQueue;
  
  function __emscripten_notify_task_queue(targetThreadId, currThreadId, mainThreadId, queue) {
      if (targetThreadId == currThreadId) {
        setTimeout(() => executeNotifiedProxyingQueue(queue));
      } else if (ENVIRONMENT_IS_PTHREAD) {
        postMessage({'targetThread' : targetThreadId, 'cmd' : 'processProxyingQueue', 'queue' : queue});
      } else {
        var worker = PThread.pthreads[targetThreadId];
        if (!worker) {
          err('Cannot send message to thread with ID ' + targetThreadId + ', unknown thread ID!');
          return /*0*/;
        }
        worker.postMessage({'cmd' : 'processProxyingQueue', 'queue': queue});
      }
    }

  function __emscripten_set_offscreencanvas_size(target, width, height) {
      err('emscripten_set_offscreencanvas_size: Build with -sOFFSCREENCANVAS_SUPPORT=1 to enable transferring canvases to pthreads.');
      return -1;
    }

  function _abort() {
      abort('native code called abort()');
    }

  var readEmAsmArgsArray = [];
  function readEmAsmArgs(sigPtr, buf) {
      // Nobody should have mutated _readEmAsmArgsArray underneath us to be something else than an array.
      assert(Array.isArray(readEmAsmArgsArray));
      // The input buffer is allocated on the stack, so it must be stack-aligned.
      assert(buf % 16 == 0);
      readEmAsmArgsArray.length = 0;
      var ch;
      // Most arguments are i32s, so shift the buffer pointer so it is a plain
      // index into HEAP32.
      buf >>= 2;
      while (ch = HEAPU8[sigPtr++]) {
        var chr = String.fromCharCode(ch);
        var validChars = ['d', 'f', 'i'];
        // In WASM_BIGINT mode we support passing i64 values as bigint.
        validChars.push('j');
        assert(validChars.includes(chr), 'Invalid character ' + ch + '("' + chr + '") in readEmAsmArgs! Use only [' + validChars + '], and do not specify "v" for void return argument.');
        // Floats are always passed as doubles, and doubles and int64s take up 8
        // bytes (two 32-bit slots) in memory, align reads to these:
        buf += (ch != 105/*i*/) & buf;
        readEmAsmArgsArray.push(
          ch == 105/*i*/ ? HEAP32[buf] :
         (ch == 106/*j*/ ? HEAP64 : HEAPF64)[buf++ >> 1]
        );
        ++buf;
      }
      return readEmAsmArgsArray;
    }
  function runMainThreadEmAsm(code, sigPtr, argbuf, sync) {
      var args = readEmAsmArgs(sigPtr, argbuf);
      if (ENVIRONMENT_IS_PTHREAD) {
        // EM_ASM functions are variadic, receiving the actual arguments as a buffer
        // in memory. the last parameter (argBuf) points to that data. We need to
        // always un-variadify that, *before proxying*, as in the async case this
        // is a stack allocation that LLVM made, which may go away before the main
        // thread gets the message. For that reason we handle proxying *after* the
        // call to readEmAsmArgs, and therefore we do that manually here instead
        // of using __proxy. (And dor simplicity, do the same in the sync
        // case as well, even though it's not strictly necessary, to keep the two
        // code paths as similar as possible on both sides.)
        // -1 - code is the encoding of a proxied EM_ASM, as a negative number
        // (positive numbers are non-EM_ASM calls).
        return _emscripten_proxy_to_main_thread_js.apply(null, [-1 - code, sync].concat(args));
      }
      if (!ASM_CONSTS.hasOwnProperty(code)) abort('No EM_ASM constant found at address ' + code);
      return ASM_CONSTS[code].apply(null, args);
    }
  function _emscripten_asm_const_async_on_main_thread(code, sigPtr, argbuf) {
      return runMainThreadEmAsm(code, sigPtr, argbuf, 0);
    }

  
  function _emscripten_check_blocking_allowed() {
      if (ENVIRONMENT_IS_NODE) return;
  
      if (ENVIRONMENT_IS_WORKER) return; // Blocking in a worker/pthread is fine.
  
      warnOnce('Blocking on the main thread is very dangerous, see https://emscripten.org/docs/porting/pthreads.html#blocking-on-the-main-browser-thread');
  
    }

  function _emscripten_date_now() {
      return Date.now();
    }

  var _emscripten_get_now;if (ENVIRONMENT_IS_NODE) {
    _emscripten_get_now = () => {
      var t = process.hrtime();
      return t[0] * 1e3 + t[1] / 1e6;
    };
  } else _emscripten_get_now = () => performance.timeOrigin + performance.now();
  ;

  function _emscripten_memcpy_big(dest, src, num) {
      HEAPU8.copyWithin(dest, src, src + num);
    }

  
  
  /** @type{function(number, (number|boolean), ...(number|boolean))} */
  function _emscripten_proxy_to_main_thread_js(index, sync) {
      // Additional arguments are passed after those two, which are the actual
      // function arguments.
      // The serialization buffer contains the number of call params, and then
      // all the args here.
      // We also pass 'sync' to C separately, since C needs to look at it.
      var numCallArgs = arguments.length - 2;
      var outerArgs = arguments;
      var maxArgs = 19;
      if (numCallArgs > maxArgs) {
        throw 'emscripten_proxy_to_main_thread_js: Too many arguments ' + numCallArgs + ' to proxied function idx=' + index + ', maximum supported is ' + maxArgs;
      }
      // Allocate a buffer, which will be copied by the C code.
      return withStackSave(() => {
        // First passed parameter specifies the number of arguments to the function.
        // When BigInt support is enabled, we must handle types in a more complex
        // way, detecting at runtime if a value is a BigInt or not (as we have no
        // type info here). To do that, add a "prefix" before each value that
        // indicates if it is a BigInt, which effectively doubles the number of
        // values we serialize for proxying. TODO: pack this?
        var serializedNumCallArgs = numCallArgs * 2;
        var args = stackAlloc(serializedNumCallArgs * 8);
        var b = args >> 3;
        for (var i = 0; i < numCallArgs; i++) {
          var arg = outerArgs[2 + i];
          if (typeof arg == 'bigint') {
            // The prefix is non-zero to indicate a bigint.
            HEAP64[b + 2*i] = 1n;
            HEAP64[b + 2*i + 1] = arg;
          } else {
            // The prefix is zero to indicate a JS Number.
            HEAP64[b + 2*i] = 0n;
            HEAPF64[b + 2*i + 1] = arg;
          }
        }
        return __emscripten_run_in_main_runtime_thread_js(index, serializedNumCallArgs, args, sync);
      });
    }
  
  var _emscripten_receive_on_main_thread_js_callArgs = [];
  
  function _emscripten_receive_on_main_thread_js(index, numCallArgs, args) {
      numCallArgs /= 2;
      _emscripten_receive_on_main_thread_js_callArgs.length = numCallArgs;
      var b = args >> 3;
      for (var i = 0; i < numCallArgs; i++) {
        if (HEAP64[b + 2*i]) {
          // It's a BigInt.
          _emscripten_receive_on_main_thread_js_callArgs[i] = HEAP64[b + 2*i + 1];
        } else {
          // It's a Number.
          _emscripten_receive_on_main_thread_js_callArgs[i] = HEAPF64[b + 2*i + 1];
        }
      }
      // Proxied JS library funcs are encoded as positive values, and
      // EM_ASMs as negative values (see include_asm_consts)
      var isEmAsmConst = index < 0;
      var func = !isEmAsmConst ? proxiedFunctionTable[index] : ASM_CONSTS[-index - 1];
      assert(func.length == numCallArgs, 'Call args mismatch in emscripten_receive_on_main_thread_js');
      return func.apply(null, _emscripten_receive_on_main_thread_js_callArgs);
    }

  function getHeapMax() {
      return HEAPU8.length;
    }
  
  function abortOnCannotGrowMemory(requestedSize) {
      abort('Cannot enlarge memory arrays to size ' + requestedSize + ' bytes (OOM). Either (1) compile with -sINITIAL_MEMORY=X with X higher than the current value ' + HEAP8.length + ', (2) compile with -sALLOW_MEMORY_GROWTH which allows increasing the size at runtime, or (3) if you want malloc to return NULL (0) instead of this abort, compile with -sABORTING_MALLOC=0');
    }
  function _emscripten_resize_heap(requestedSize) {
      var oldSize = HEAPU8.length;
      requestedSize = requestedSize >>> 0;
      abortOnCannotGrowMemory(requestedSize);
    }

  function _emscripten_unwind_to_js_event_loop() {
      throw 'unwind';
    }

  var ENV = {};
  
  function getExecutableName() {
      return thisProgram || './this.program';
    }
  function getEnvStrings() {
      if (!getEnvStrings.strings) {
        // Default values.
        // Browser language detection #8751
        var lang = ((typeof navigator == 'object' && navigator.languages && navigator.languages[0]) || 'C').replace('-', '_') + '.UTF-8';
        var env = {
          'USER': 'web_user',
          'LOGNAME': 'web_user',
          'PATH': '/',
          'PWD': '/',
          'HOME': '/home/web_user',
          'LANG': lang,
          '_': getExecutableName()
        };
        // Apply the user-provided values, if any.
        for (var x in ENV) {
          // x is a key in ENV; if ENV[x] is undefined, that means it was
          // explicitly set to be so. We allow user code to do that to
          // force variables with default values to remain unset.
          if (ENV[x] === undefined) delete env[x];
          else env[x] = ENV[x];
        }
        var strings = [];
        for (var x in env) {
          strings.push(x + '=' + env[x]);
        }
        getEnvStrings.strings = strings;
      }
      return getEnvStrings.strings;
    }
  
  /** @param {boolean=} dontAddNull */
  function writeAsciiToMemory(str, buffer, dontAddNull) {
      for (var i = 0; i < str.length; ++i) {
        assert(str.charCodeAt(i) === (str.charCodeAt(i) & 0xff));
        HEAP8[((buffer++)>>0)] = str.charCodeAt(i);
      }
      // Null-terminate the pointer to the HEAP.
      if (!dontAddNull) HEAP8[((buffer)>>0)] = 0;
    }
  
  
  function _environ_get(__environ, environ_buf) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(7, 1, __environ, environ_buf);
  
      var bufSize = 0;
      getEnvStrings().forEach(function(string, i) {
        var ptr = environ_buf + bufSize;
        HEAPU32[(((__environ)+(i*4))>>2)] = ptr;
        writeAsciiToMemory(string, ptr);
        bufSize += string.length + 1;
      });
      return 0;
    
  }
  

  
  
  function _environ_sizes_get(penviron_count, penviron_buf_size) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(8, 1, penviron_count, penviron_buf_size);
  
      var strings = getEnvStrings();
      HEAPU32[((penviron_count)>>2)] = strings.length;
      var bufSize = 0;
      strings.forEach(function(string) {
        bufSize += string.length + 1;
      });
      HEAPU32[((penviron_buf_size)>>2)] = bufSize;
      return 0;
    
  }
  


  
  function _fd_close(fd) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(9, 1, fd);
  
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      FS.close(stream);
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  
  }
  

  /** @param {number=} offset */
  function doReadv(stream, iov, iovcnt, offset) {
      var ret = 0;
      for (var i = 0; i < iovcnt; i++) {
        var ptr = HEAPU32[((iov)>>2)];
        var len = HEAPU32[(((iov)+(4))>>2)];
        iov += 8;
        var curr = FS.read(stream, HEAP8,ptr, len, offset);
        if (curr < 0) return -1;
        ret += curr;
        if (curr < len) break; // nothing more to read
        if (typeof offset !== 'undefined') {
          offset += curr;
        }
      }
      return ret;
    }
  
  
  function _fd_read(fd, iov, iovcnt, pnum) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(10, 1, fd, iov, iovcnt, pnum);
  
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      var num = doReadv(stream, iov, iovcnt);
      HEAPU32[((pnum)>>2)] = num;
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  
  }
  

  var MAX_INT53 = 9007199254740992;
  
  var MIN_INT53 = -9007199254740992;
  function bigintToI53Checked(num) {
      return (num < MIN_INT53 || num > MAX_INT53) ? NaN : Number(num);
    }
  
  
  
  
  
  function _fd_seek(fd, /** @type {!BigInt} */ offset, whence, newOffset) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(11, 1, fd, /** @type {!BigInt} */ offset, whence, newOffset);
  
  try {
  
      offset = bigintToI53Checked(offset); if (isNaN(offset)) return 61;
      var stream = SYSCALLS.getStreamFromFD(fd);
      FS.llseek(stream, offset, whence);
      (tempI64 = [stream.position>>>0,(tempDouble=stream.position,(+(Math.abs(tempDouble))) >= 1.0 ? (tempDouble > 0.0 ? ((Math.min((+(Math.floor((tempDouble)/4294967296.0))), 4294967295.0))|0)>>>0 : (~~((+(Math.ceil((tempDouble - +(((~~(tempDouble)))>>>0))/4294967296.0)))))>>>0) : 0)],HEAP32[((newOffset)>>2)] = tempI64[0],HEAP32[(((newOffset)+(4))>>2)] = tempI64[1]);
      if (stream.getdents && offset === 0 && whence === 0) stream.getdents = null; // reset readdir state
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  
  }
  

  /** @param {number=} offset */
  function doWritev(stream, iov, iovcnt, offset) {
      var ret = 0;
      for (var i = 0; i < iovcnt; i++) {
        var ptr = HEAPU32[((iov)>>2)];
        var len = HEAPU32[(((iov)+(4))>>2)];
        iov += 8;
        var curr = FS.write(stream, HEAP8,ptr, len, offset);
        if (curr < 0) return -1;
        ret += curr;
        if (typeof offset !== 'undefined') {
          offset += curr;
        }
      }
      return ret;
    }
  
  
  function _fd_write(fd, iov, iovcnt, pnum) {
  if (ENVIRONMENT_IS_PTHREAD)
    return _emscripten_proxy_to_main_thread_js(12, 1, fd, iov, iovcnt, pnum);
  
  try {
  
      var stream = SYSCALLS.getStreamFromFD(fd);
      var num = doWritev(stream, iov, iovcnt);
      HEAPU32[((pnum)>>2)] = num;
      return 0;
    } catch (e) {
    if (typeof FS == 'undefined' || !(e.name === 'ErrnoError')) throw e;
    return e.errno;
  }
  
  }
  

  function _llvm_eh_typeid_for(type) {
      return type;
    }


  function __isLeapYear(year) {
        return year%4 === 0 && (year%100 !== 0 || year%400 === 0);
    }
  
  function __arraySum(array, index) {
      var sum = 0;
      for (var i = 0; i <= index; sum += array[i++]) {
        // no-op
      }
      return sum;
    }
  
  
  var __MONTH_DAYS_LEAP = [31,29,31,30,31,30,31,31,30,31,30,31];
  
  var __MONTH_DAYS_REGULAR = [31,28,31,30,31,30,31,31,30,31,30,31];
  function __addDays(date, days) {
      var newDate = new Date(date.getTime());
      while (days > 0) {
        var leap = __isLeapYear(newDate.getFullYear());
        var currentMonth = newDate.getMonth();
        var daysInCurrentMonth = (leap ? __MONTH_DAYS_LEAP : __MONTH_DAYS_REGULAR)[currentMonth];
  
        if (days > daysInCurrentMonth-newDate.getDate()) {
          // we spill over to next month
          days -= (daysInCurrentMonth-newDate.getDate()+1);
          newDate.setDate(1);
          if (currentMonth < 11) {
            newDate.setMonth(currentMonth+1)
          } else {
            newDate.setMonth(0);
            newDate.setFullYear(newDate.getFullYear()+1);
          }
        } else {
          // we stay in current month
          newDate.setDate(newDate.getDate()+days);
          return newDate;
        }
      }
  
      return newDate;
    }
  
  
  
  
  function writeArrayToMemory(array, buffer) {
      assert(array.length >= 0, 'writeArrayToMemory array must have a length (should be an array or typed array)')
      HEAP8.set(array, buffer);
    }
  function _strftime(s, maxsize, format, tm) {
      // size_t strftime(char *restrict s, size_t maxsize, const char *restrict format, const struct tm *restrict timeptr);
      // http://pubs.opengroup.org/onlinepubs/009695399/functions/strftime.html
  
      var tm_zone = HEAP32[(((tm)+(40))>>2)];
  
      var date = {
        tm_sec: HEAP32[((tm)>>2)],
        tm_min: HEAP32[(((tm)+(4))>>2)],
        tm_hour: HEAP32[(((tm)+(8))>>2)],
        tm_mday: HEAP32[(((tm)+(12))>>2)],
        tm_mon: HEAP32[(((tm)+(16))>>2)],
        tm_year: HEAP32[(((tm)+(20))>>2)],
        tm_wday: HEAP32[(((tm)+(24))>>2)],
        tm_yday: HEAP32[(((tm)+(28))>>2)],
        tm_isdst: HEAP32[(((tm)+(32))>>2)],
        tm_gmtoff: HEAP32[(((tm)+(36))>>2)],
        tm_zone: tm_zone ? UTF8ToString(tm_zone) : ''
      };
  
      var pattern = UTF8ToString(format);
  
      // expand format
      var EXPANSION_RULES_1 = {
        '%c': '%a %b %d %H:%M:%S %Y',     // Replaced by the locale's appropriate date and time representation - e.g., Mon Aug  3 14:02:01 2013
        '%D': '%m/%d/%y',                 // Equivalent to %m / %d / %y
        '%F': '%Y-%m-%d',                 // Equivalent to %Y - %m - %d
        '%h': '%b',                       // Equivalent to %b
        '%r': '%I:%M:%S %p',              // Replaced by the time in a.m. and p.m. notation
        '%R': '%H:%M',                    // Replaced by the time in 24-hour notation
        '%T': '%H:%M:%S',                 // Replaced by the time
        '%x': '%m/%d/%y',                 // Replaced by the locale's appropriate date representation
        '%X': '%H:%M:%S',                 // Replaced by the locale's appropriate time representation
        // Modified Conversion Specifiers
        '%Ec': '%c',                      // Replaced by the locale's alternative appropriate date and time representation.
        '%EC': '%C',                      // Replaced by the name of the base year (period) in the locale's alternative representation.
        '%Ex': '%m/%d/%y',                // Replaced by the locale's alternative date representation.
        '%EX': '%H:%M:%S',                // Replaced by the locale's alternative time representation.
        '%Ey': '%y',                      // Replaced by the offset from %EC (year only) in the locale's alternative representation.
        '%EY': '%Y',                      // Replaced by the full alternative year representation.
        '%Od': '%d',                      // Replaced by the day of the month, using the locale's alternative numeric symbols, filled as needed with leading zeros if there is any alternative symbol for zero; otherwise, with leading <space> characters.
        '%Oe': '%e',                      // Replaced by the day of the month, using the locale's alternative numeric symbols, filled as needed with leading <space> characters.
        '%OH': '%H',                      // Replaced by the hour (24-hour clock) using the locale's alternative numeric symbols.
        '%OI': '%I',                      // Replaced by the hour (12-hour clock) using the locale's alternative numeric symbols.
        '%Om': '%m',                      // Replaced by the month using the locale's alternative numeric symbols.
        '%OM': '%M',                      // Replaced by the minutes using the locale's alternative numeric symbols.
        '%OS': '%S',                      // Replaced by the seconds using the locale's alternative numeric symbols.
        '%Ou': '%u',                      // Replaced by the weekday as a number in the locale's alternative representation (Monday=1).
        '%OU': '%U',                      // Replaced by the week number of the year (Sunday as the first day of the week, rules corresponding to %U ) using the locale's alternative numeric symbols.
        '%OV': '%V',                      // Replaced by the week number of the year (Monday as the first day of the week, rules corresponding to %V ) using the locale's alternative numeric symbols.
        '%Ow': '%w',                      // Replaced by the number of the weekday (Sunday=0) using the locale's alternative numeric symbols.
        '%OW': '%W',                      // Replaced by the week number of the year (Monday as the first day of the week) using the locale's alternative numeric symbols.
        '%Oy': '%y',                      // Replaced by the year (offset from %C ) using the locale's alternative numeric symbols.
      };
      for (var rule in EXPANSION_RULES_1) {
        pattern = pattern.replace(new RegExp(rule, 'g'), EXPANSION_RULES_1[rule]);
      }
  
      var WEEKDAYS = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
      var MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
  
      function leadingSomething(value, digits, character) {
        var str = typeof value == 'number' ? value.toString() : (value || '');
        while (str.length < digits) {
          str = character[0]+str;
        }
        return str;
      }
  
      function leadingNulls(value, digits) {
        return leadingSomething(value, digits, '0');
      }
  
      function compareByDay(date1, date2) {
        function sgn(value) {
          return value < 0 ? -1 : (value > 0 ? 1 : 0);
        }
  
        var compare;
        if ((compare = sgn(date1.getFullYear()-date2.getFullYear())) === 0) {
          if ((compare = sgn(date1.getMonth()-date2.getMonth())) === 0) {
            compare = sgn(date1.getDate()-date2.getDate());
          }
        }
        return compare;
      }
  
      function getFirstWeekStartDate(janFourth) {
          switch (janFourth.getDay()) {
            case 0: // Sunday
              return new Date(janFourth.getFullYear()-1, 11, 29);
            case 1: // Monday
              return janFourth;
            case 2: // Tuesday
              return new Date(janFourth.getFullYear(), 0, 3);
            case 3: // Wednesday
              return new Date(janFourth.getFullYear(), 0, 2);
            case 4: // Thursday
              return new Date(janFourth.getFullYear(), 0, 1);
            case 5: // Friday
              return new Date(janFourth.getFullYear()-1, 11, 31);
            case 6: // Saturday
              return new Date(janFourth.getFullYear()-1, 11, 30);
          }
      }
  
      function getWeekBasedYear(date) {
          var thisDate = __addDays(new Date(date.tm_year+1900, 0, 1), date.tm_yday);
  
          var janFourthThisYear = new Date(thisDate.getFullYear(), 0, 4);
          var janFourthNextYear = new Date(thisDate.getFullYear()+1, 0, 4);
  
          var firstWeekStartThisYear = getFirstWeekStartDate(janFourthThisYear);
          var firstWeekStartNextYear = getFirstWeekStartDate(janFourthNextYear);
  
          if (compareByDay(firstWeekStartThisYear, thisDate) <= 0) {
            // this date is after the start of the first week of this year
            if (compareByDay(firstWeekStartNextYear, thisDate) <= 0) {
              return thisDate.getFullYear()+1;
            }
            return thisDate.getFullYear();
          }
          return thisDate.getFullYear()-1;
      }
  
      var EXPANSION_RULES_2 = {
        '%a': function(date) {
          return WEEKDAYS[date.tm_wday].substring(0,3);
        },
        '%A': function(date) {
          return WEEKDAYS[date.tm_wday];
        },
        '%b': function(date) {
          return MONTHS[date.tm_mon].substring(0,3);
        },
        '%B': function(date) {
          return MONTHS[date.tm_mon];
        },
        '%C': function(date) {
          var year = date.tm_year+1900;
          return leadingNulls((year/100)|0,2);
        },
        '%d': function(date) {
          return leadingNulls(date.tm_mday, 2);
        },
        '%e': function(date) {
          return leadingSomething(date.tm_mday, 2, ' ');
        },
        '%g': function(date) {
          // %g, %G, and %V give values according to the ISO 8601:2000 standard week-based year.
          // In this system, weeks begin on a Monday and week 1 of the year is the week that includes
          // January 4th, which is also the week that includes the first Thursday of the year, and
          // is also the first week that contains at least four days in the year.
          // If the first Monday of January is the 2nd, 3rd, or 4th, the preceding days are part of
          // the last week of the preceding year; thus, for Saturday 2nd January 1999,
          // %G is replaced by 1998 and %V is replaced by 53. If December 29th, 30th,
          // or 31st is a Monday, it and any following days are part of week 1 of the following year.
          // Thus, for Tuesday 30th December 1997, %G is replaced by 1998 and %V is replaced by 01.
  
          return getWeekBasedYear(date).toString().substring(2);
        },
        '%G': function(date) {
          return getWeekBasedYear(date);
        },
        '%H': function(date) {
          return leadingNulls(date.tm_hour, 2);
        },
        '%I': function(date) {
          var twelveHour = date.tm_hour;
          if (twelveHour == 0) twelveHour = 12;
          else if (twelveHour > 12) twelveHour -= 12;
          return leadingNulls(twelveHour, 2);
        },
        '%j': function(date) {
          // Day of the year (001-366)
          return leadingNulls(date.tm_mday+__arraySum(__isLeapYear(date.tm_year+1900) ? __MONTH_DAYS_LEAP : __MONTH_DAYS_REGULAR, date.tm_mon-1), 3);
        },
        '%m': function(date) {
          return leadingNulls(date.tm_mon+1, 2);
        },
        '%M': function(date) {
          return leadingNulls(date.tm_min, 2);
        },
        '%n': function() {
          return '\n';
        },
        '%p': function(date) {
          if (date.tm_hour >= 0 && date.tm_hour < 12) {
            return 'AM';
          }
          return 'PM';
        },
        '%S': function(date) {
          return leadingNulls(date.tm_sec, 2);
        },
        '%t': function() {
          return '\t';
        },
        '%u': function(date) {
          return date.tm_wday || 7;
        },
        '%U': function(date) {
          var days = date.tm_yday + 7 - date.tm_wday;
          return leadingNulls(Math.floor(days / 7), 2);
        },
        '%V': function(date) {
          // Replaced by the week number of the year (Monday as the first day of the week)
          // as a decimal number [01,53]. If the week containing 1 January has four
          // or more days in the new year, then it is considered week 1.
          // Otherwise, it is the last week of the previous year, and the next week is week 1.
          // Both January 4th and the first Thursday of January are always in week 1. [ tm_year, tm_wday, tm_yday]
          var val = Math.floor((date.tm_yday + 7 - (date.tm_wday + 6) % 7 ) / 7);
          // If 1 Jan is just 1-3 days past Monday, the previous week
          // is also in this year.
          if ((date.tm_wday + 371 - date.tm_yday - 2) % 7 <= 2) {
            val++;
          }
          if (!val) {
            val = 52;
            // If 31 December of prev year a Thursday, or Friday of a
            // leap year, then the prev year has 53 weeks.
            var dec31 = (date.tm_wday + 7 - date.tm_yday - 1) % 7;
            if (dec31 == 4 || (dec31 == 5 && __isLeapYear(date.tm_year%400-1))) {
              val++;
            }
          } else if (val == 53) {
            // If 1 January is not a Thursday, and not a Wednesday of a
            // leap year, then this year has only 52 weeks.
            var jan1 = (date.tm_wday + 371 - date.tm_yday) % 7;
            if (jan1 != 4 && (jan1 != 3 || !__isLeapYear(date.tm_year)))
              val = 1;
          }
          return leadingNulls(val, 2);
        },
        '%w': function(date) {
          return date.tm_wday;
        },
        '%W': function(date) {
          var days = date.tm_yday + 7 - ((date.tm_wday + 6) % 7);
          return leadingNulls(Math.floor(days / 7), 2);
        },
        '%y': function(date) {
          // Replaced by the last two digits of the year as a decimal number [00,99]. [ tm_year]
          return (date.tm_year+1900).toString().substring(2);
        },
        '%Y': function(date) {
          // Replaced by the year as a decimal number (for example, 1997). [ tm_year]
          return date.tm_year+1900;
        },
        '%z': function(date) {
          // Replaced by the offset from UTC in the ISO 8601:2000 standard format ( +hhmm or -hhmm ).
          // For example, "-0430" means 4 hours 30 minutes behind UTC (west of Greenwich).
          var off = date.tm_gmtoff;
          var ahead = off >= 0;
          off = Math.abs(off) / 60;
          // convert from minutes into hhmm format (which means 60 minutes = 100 units)
          off = (off / 60)*100 + (off % 60);
          return (ahead ? '+' : '-') + String("0000" + off).slice(-4);
        },
        '%Z': function(date) {
          return date.tm_zone;
        },
        '%%': function() {
          return '%';
        }
      };
  
      // Replace %% with a pair of NULLs (which cannot occur in a C string), then
      // re-inject them after processing.
      pattern = pattern.replace(/%%/g, '\0\0')
      for (var rule in EXPANSION_RULES_2) {
        if (pattern.includes(rule)) {
          pattern = pattern.replace(new RegExp(rule, 'g'), EXPANSION_RULES_2[rule](date));
        }
      }
      pattern = pattern.replace(/\0\0/g, '%')
  
      var bytes = intArrayFromString(pattern, false);
      if (bytes.length > maxsize) {
        return 0;
      }
  
      writeArrayToMemory(bytes, s);
      return bytes.length-1;
    }
  function _strftime_l(s, maxsize, format, tm, loc) {
      return _strftime(s, maxsize, format, tm); // no locale support yet
    }


  function getCFunc(ident) {
      var func = Module['_' + ident]; // closure exported function
      assert(func, 'Cannot call unknown function ' + ident + ', make sure it is exported');
      return func;
    }
  
  
    /**
     * @param {string|null=} returnType
     * @param {Array=} argTypes
     * @param {Arguments|Array=} args
     * @param {Object=} opts
     */
  function ccall(ident, returnType, argTypes, args, opts) {
      // For fast lookup of conversion functions
      var toC = {
        'string': (str) => {
          var ret = 0;
          if (str !== null && str !== undefined && str !== 0) { // null string
            // at most 4 bytes per UTF-8 code point, +1 for the trailing '\0'
            var len = (str.length << 2) + 1;
            ret = stackAlloc(len);
            stringToUTF8(str, ret, len);
          }
          return ret;
        },
        'array': (arr) => {
          var ret = stackAlloc(arr.length);
          writeArrayToMemory(arr, ret);
          return ret;
        }
      };
  
      function convertReturnValue(ret) {
        if (returnType === 'string') {
          
          return UTF8ToString(ret);
        }
        if (returnType === 'boolean') return Boolean(ret);
        return ret;
      }
  
      var func = getCFunc(ident);
      var cArgs = [];
      var stack = 0;
      assert(returnType !== 'array', 'Return type should not be "array".');
      if (args) {
        for (var i = 0; i < args.length; i++) {
          var converter = toC[argTypes[i]];
          if (converter) {
            if (stack === 0) stack = stackSave();
            cArgs[i] = converter(args[i]);
          } else {
            cArgs[i] = args[i];
          }
        }
      }
      var ret = func.apply(null, cArgs);
      function onDone(ret) {
        if (stack !== 0) stackRestore(stack);
        return convertReturnValue(ret);
      }
  
      ret = onDone(ret);
      return ret;
    }


  var ALLOC_NORMAL = 0;
  
  var ALLOC_STACK = 1;
  function allocate(slab, allocator) {
      var ret;
      assert(typeof allocator == 'number', 'allocate no longer takes a type argument')
      assert(typeof slab != 'number', 'allocate no longer takes a number as arg0')
  
      if (allocator == ALLOC_STACK) {
        ret = stackAlloc(slab.length);
      } else {
        ret = _malloc(slab.length);
      }
  
      if (!slab.subarray && !slab.slice) {
        slab = new Uint8Array(slab);
      }
      HEAPU8.set(slab, ret);
      return ret;
    }





PThread.init();;

  var FSNode = /** @constructor */ function(parent, name, mode, rdev) {
    if (!parent) {
      parent = this;  // root node sets parent to itself
    }
    this.parent = parent;
    this.mount = parent.mount;
    this.mounted = null;
    this.id = FS.nextInode++;
    this.name = name;
    this.mode = mode;
    this.node_ops = {};
    this.stream_ops = {};
    this.rdev = rdev;
  };
  var readMode = 292/*292*/ | 73/*73*/;
  var writeMode = 146/*146*/;
  Object.defineProperties(FSNode.prototype, {
   read: {
    get: /** @this{FSNode} */function() {
     return (this.mode & readMode) === readMode;
    },
    set: /** @this{FSNode} */function(val) {
     val ? this.mode |= readMode : this.mode &= ~readMode;
    }
   },
   write: {
    get: /** @this{FSNode} */function() {
     return (this.mode & writeMode) === writeMode;
    },
    set: /** @this{FSNode} */function(val) {
     val ? this.mode |= writeMode : this.mode &= ~writeMode;
    }
   },
   isFolder: {
    get: /** @this{FSNode} */function() {
     return FS.isDir(this.mode);
    }
   },
   isDevice: {
    get: /** @this{FSNode} */function() {
     return FS.isChrdev(this.mode);
    }
   }
  });
  FS.FSNode = FSNode;
  FS.staticInit();;
ERRNO_CODES = {
      'EPERM': 63,
      'ENOENT': 44,
      'ESRCH': 71,
      'EINTR': 27,
      'EIO': 29,
      'ENXIO': 60,
      'E2BIG': 1,
      'ENOEXEC': 45,
      'EBADF': 8,
      'ECHILD': 12,
      'EAGAIN': 6,
      'EWOULDBLOCK': 6,
      'ENOMEM': 48,
      'EACCES': 2,
      'EFAULT': 21,
      'ENOTBLK': 105,
      'EBUSY': 10,
      'EEXIST': 20,
      'EXDEV': 75,
      'ENODEV': 43,
      'ENOTDIR': 54,
      'EISDIR': 31,
      'EINVAL': 28,
      'ENFILE': 41,
      'EMFILE': 33,
      'ENOTTY': 59,
      'ETXTBSY': 74,
      'EFBIG': 22,
      'ENOSPC': 51,
      'ESPIPE': 70,
      'EROFS': 69,
      'EMLINK': 34,
      'EPIPE': 64,
      'EDOM': 18,
      'ERANGE': 68,
      'ENOMSG': 49,
      'EIDRM': 24,
      'ECHRNG': 106,
      'EL2NSYNC': 156,
      'EL3HLT': 107,
      'EL3RST': 108,
      'ELNRNG': 109,
      'EUNATCH': 110,
      'ENOCSI': 111,
      'EL2HLT': 112,
      'EDEADLK': 16,
      'ENOLCK': 46,
      'EBADE': 113,
      'EBADR': 114,
      'EXFULL': 115,
      'ENOANO': 104,
      'EBADRQC': 103,
      'EBADSLT': 102,
      'EDEADLOCK': 16,
      'EBFONT': 101,
      'ENOSTR': 100,
      'ENODATA': 116,
      'ETIME': 117,
      'ENOSR': 118,
      'ENONET': 119,
      'ENOPKG': 120,
      'EREMOTE': 121,
      'ENOLINK': 47,
      'EADV': 122,
      'ESRMNT': 123,
      'ECOMM': 124,
      'EPROTO': 65,
      'EMULTIHOP': 36,
      'EDOTDOT': 125,
      'EBADMSG': 9,
      'ENOTUNIQ': 126,
      'EBADFD': 127,
      'EREMCHG': 128,
      'ELIBACC': 129,
      'ELIBBAD': 130,
      'ELIBSCN': 131,
      'ELIBMAX': 132,
      'ELIBEXEC': 133,
      'ENOSYS': 52,
      'ENOTEMPTY': 55,
      'ENAMETOOLONG': 37,
      'ELOOP': 32,
      'EOPNOTSUPP': 138,
      'EPFNOSUPPORT': 139,
      'ECONNRESET': 15,
      'ENOBUFS': 42,
      'EAFNOSUPPORT': 5,
      'EPROTOTYPE': 67,
      'ENOTSOCK': 57,
      'ENOPROTOOPT': 50,
      'ESHUTDOWN': 140,
      'ECONNREFUSED': 14,
      'EADDRINUSE': 3,
      'ECONNABORTED': 13,
      'ENETUNREACH': 40,
      'ENETDOWN': 38,
      'ETIMEDOUT': 73,
      'EHOSTDOWN': 142,
      'EHOSTUNREACH': 23,
      'EINPROGRESS': 26,
      'EALREADY': 7,
      'EDESTADDRREQ': 17,
      'EMSGSIZE': 35,
      'EPROTONOSUPPORT': 66,
      'ESOCKTNOSUPPORT': 137,
      'EADDRNOTAVAIL': 4,
      'ENETRESET': 39,
      'EISCONN': 30,
      'ENOTCONN': 53,
      'ETOOMANYREFS': 141,
      'EUSERS': 136,
      'EDQUOT': 19,
      'ESTALE': 72,
      'ENOTSUP': 138,
      'ENOMEDIUM': 148,
      'EILSEQ': 25,
      'EOVERFLOW': 61,
      'ECANCELED': 11,
      'ENOTRECOVERABLE': 56,
      'EOWNERDEAD': 62,
      'ESTRPIPE': 135,
    };;

 // proxiedFunctionTable specifies the list of functions that can be called either synchronously or asynchronously from other threads in postMessage()d or internally queued events. This way a pthread in a Worker can synchronously access e.g. the DOM on the main thread.

var proxiedFunctionTable = [null,_proc_exit,exitOnMainThread,pthreadCreateProxied,___syscall_fcntl64,___syscall_ioctl,___syscall_openat,_environ_get,_environ_sizes_get,_fd_close,_fd_read,_fd_seek,_fd_write];

function checkIncomingModuleAPI() {
  ignoredModuleProp('fetchSettings');
}
var wasmImports = {
  "__assert_fail": ___assert_fail,
  "__call_sighandler": ___call_sighandler,
  "__cxa_begin_catch": ___cxa_begin_catch,
  "__cxa_end_catch": ___cxa_end_catch,
  "__cxa_find_matching_catch_2": ___cxa_find_matching_catch_2,
  "__cxa_find_matching_catch_3": ___cxa_find_matching_catch_3,
  "__cxa_find_matching_catch_4": ___cxa_find_matching_catch_4,
  "__cxa_find_matching_catch_7": ___cxa_find_matching_catch_7,
  "__cxa_find_matching_catch_8": ___cxa_find_matching_catch_8,
  "__cxa_rethrow": ___cxa_rethrow,
  "__cxa_throw": ___cxa_throw,
  "__cxa_uncaught_exceptions": ___cxa_uncaught_exceptions,
  "__emscripten_init_main_thread_js": ___emscripten_init_main_thread_js,
  "__emscripten_thread_cleanup": ___emscripten_thread_cleanup,
  "__pthread_create_js": ___pthread_create_js,
  "__resumeException": ___resumeException,
  "__syscall_fcntl64": ___syscall_fcntl64,
  "__syscall_ioctl": ___syscall_ioctl,
  "__syscall_openat": ___syscall_openat,
  "_emscripten_default_pthread_stack_size": __emscripten_default_pthread_stack_size,
  "_emscripten_get_now_is_monotonic": __emscripten_get_now_is_monotonic,
  "_emscripten_notify_task_queue": __emscripten_notify_task_queue,
  "_emscripten_set_offscreencanvas_size": __emscripten_set_offscreencanvas_size,
  "abort": _abort,
  "emscripten_asm_const_async_on_main_thread": _emscripten_asm_const_async_on_main_thread,
  "emscripten_check_blocking_allowed": _emscripten_check_blocking_allowed,
  "emscripten_date_now": _emscripten_date_now,
  "emscripten_get_now": _emscripten_get_now,
  "emscripten_memcpy_big": _emscripten_memcpy_big,
  "emscripten_receive_on_main_thread_js": _emscripten_receive_on_main_thread_js,
  "emscripten_resize_heap": _emscripten_resize_heap,
  "emscripten_unwind_to_js_event_loop": _emscripten_unwind_to_js_event_loop,
  "environ_get": _environ_get,
  "environ_sizes_get": _environ_sizes_get,
  "exit": _exit,
  "fd_close": _fd_close,
  "fd_read": _fd_read,
  "fd_seek": _fd_seek,
  "fd_write": _fd_write,
  "invoke_di": invoke_di,
  "invoke_dii": invoke_dii,
  "invoke_diid": invoke_diid,
  "invoke_diii": invoke_diii,
  "invoke_diiid": invoke_diiid,
  "invoke_fii": invoke_fii,
  "invoke_fiii": invoke_fiii,
  "invoke_fiiii": invoke_fiiii,
  "invoke_i": invoke_i,
  "invoke_id": invoke_id,
  "invoke_ii": invoke_ii,
  "invoke_iid": invoke_iid,
  "invoke_iii": invoke_iii,
  "invoke_iiid": invoke_iiid,
  "invoke_iiii": invoke_iiii,
  "invoke_iiiii": invoke_iiiii,
  "invoke_iiiiid": invoke_iiiiid,
  "invoke_iiiiii": invoke_iiiiii,
  "invoke_iiiiiii": invoke_iiiiiii,
  "invoke_iiiiiiii": invoke_iiiiiiii,
  "invoke_iiiiiiiii": invoke_iiiiiiiii,
  "invoke_iiiiiiiiii": invoke_iiiiiiiiii,
  "invoke_iiiiiiiiiii": invoke_iiiiiiiiiii,
  "invoke_iiiiiiiiiiii": invoke_iiiiiiiiiiii,
  "invoke_iiiiiiiiiiiii": invoke_iiiiiiiiiiiii,
  "invoke_iiiiiiiiiiiiii": invoke_iiiiiiiiiiiiii,
  "invoke_iiiiij": invoke_iiiiij,
  "invoke_iiij": invoke_iiij,
  "invoke_iij": invoke_iij,
  "invoke_iiji": invoke_iiji,
  "invoke_iijii": invoke_iijii,
  "invoke_j": invoke_j,
  "invoke_ji": invoke_ji,
  "invoke_jii": invoke_jii,
  "invoke_jiii": invoke_jiii,
  "invoke_jiiii": invoke_jiiii,
  "invoke_jiij": invoke_jiij,
  "invoke_v": invoke_v,
  "invoke_vi": invoke_vi,
  "invoke_vid": invoke_vid,
  "invoke_vidi": invoke_vidi,
  "invoke_vidii": invoke_vidii,
  "invoke_vifi": invoke_vifi,
  "invoke_vii": invoke_vii,
  "invoke_viid": invoke_viid,
  "invoke_viidi": invoke_viidi,
  "invoke_viii": invoke_viii,
  "invoke_viiid": invoke_viiid,
  "invoke_viiii": invoke_viiii,
  "invoke_viiiid": invoke_viiiid,
  "invoke_viiiif": invoke_viiiif,
  "invoke_viiiii": invoke_viiiii,
  "invoke_viiiiii": invoke_viiiiii,
  "invoke_viiiiiii": invoke_viiiiiii,
  "invoke_viiiiiiii": invoke_viiiiiiii,
  "invoke_viiiiiiiii": invoke_viiiiiiiii,
  "invoke_viiiiiiiiii": invoke_viiiiiiiiii,
  "invoke_viiiiiiiiiii": invoke_viiiiiiiiiii,
  "invoke_viiiiiiiiiiii": invoke_viiiiiiiiiiii,
  "invoke_viiiiiiiiiiiii": invoke_viiiiiiiiiiiii,
  "invoke_viiiiiiiiiiiiiii": invoke_viiiiiiiiiiiiiii,
  "invoke_viiiiij": invoke_viiiiij,
  "invoke_viiiiiji": invoke_viiiiiji,
  "invoke_viiiiijj": invoke_viiiiijj,
  "invoke_viij": invoke_viij,
  "invoke_viiji": invoke_viiji,
  "invoke_viijji": invoke_viijji,
  "invoke_vij": invoke_vij,
  "invoke_viji": invoke_viji,
  "invoke_vijj": invoke_vijj,
  "llvm_eh_typeid_for": _llvm_eh_typeid_for,
  "memory": wasmMemory || Module['wasmMemory'],
  "proc_exit": _proc_exit,
  "strftime_l": _strftime_l
};
var asm = createWasm();
/** @type {function(...*):?} */
var ___wasm_call_ctors = createExportWrapper("__wasm_call_ctors");
/** @type {function(...*):?} */
var _Z3_get_error_msg = Module["_Z3_get_error_msg"] = createExportWrapper("Z3_get_error_msg");
/** @type {function(...*):?} */
var getTempRet0 = createExportWrapper("getTempRet0");
/** @type {function(...*):?} */
var ___cxa_free_exception = createExportWrapper("__cxa_free_exception");
/** @type {function(...*):?} */
var _set_throwy_error_handler = Module["_set_throwy_error_handler"] = createExportWrapper("set_throwy_error_handler");
/** @type {function(...*):?} */
var _set_noop_error_handler = Module["_set_noop_error_handler"] = createExportWrapper("set_noop_error_handler");
/** @type {function(...*):?} */
var _async_Z3_eval_smtlib2_string = Module["_async_Z3_eval_smtlib2_string"] = createExportWrapper("async_Z3_eval_smtlib2_string");
/** @type {function(...*):?} */
var _async_Z3_simplify = Module["_async_Z3_simplify"] = createExportWrapper("async_Z3_simplify");
/** @type {function(...*):?} */
var _async_Z3_simplify_ex = Module["_async_Z3_simplify_ex"] = createExportWrapper("async_Z3_simplify_ex");
/** @type {function(...*):?} */
var _async_Z3_solver_check = Module["_async_Z3_solver_check"] = createExportWrapper("async_Z3_solver_check");
/** @type {function(...*):?} */
var _async_Z3_solver_check_assumptions = Module["_async_Z3_solver_check_assumptions"] = createExportWrapper("async_Z3_solver_check_assumptions");
/** @type {function(...*):?} */
var _async_Z3_solver_cube = Module["_async_Z3_solver_cube"] = createExportWrapper("async_Z3_solver_cube");
/** @type {function(...*):?} */
var _async_Z3_solver_get_consequences = Module["_async_Z3_solver_get_consequences"] = createExportWrapper("async_Z3_solver_get_consequences");
/** @type {function(...*):?} */
var _async_Z3_tactic_apply = Module["_async_Z3_tactic_apply"] = createExportWrapper("async_Z3_tactic_apply");
/** @type {function(...*):?} */
var _async_Z3_tactic_apply_ex = Module["_async_Z3_tactic_apply_ex"] = createExportWrapper("async_Z3_tactic_apply_ex");
/** @type {function(...*):?} */
var _async_Z3_optimize_check = Module["_async_Z3_optimize_check"] = createExportWrapper("async_Z3_optimize_check");
/** @type {function(...*):?} */
var _async_Z3_algebraic_roots = Module["_async_Z3_algebraic_roots"] = createExportWrapper("async_Z3_algebraic_roots");
/** @type {function(...*):?} */
var _async_Z3_algebraic_eval = Module["_async_Z3_algebraic_eval"] = createExportWrapper("async_Z3_algebraic_eval");
/** @type {function(...*):?} */
var _async_Z3_fixedpoint_query = Module["_async_Z3_fixedpoint_query"] = createExportWrapper("async_Z3_fixedpoint_query");
/** @type {function(...*):?} */
var _async_Z3_fixedpoint_query_relations = Module["_async_Z3_fixedpoint_query_relations"] = createExportWrapper("async_Z3_fixedpoint_query_relations");
/** @type {function(...*):?} */
var _async_Z3_fixedpoint_query_from_lvl = Module["_async_Z3_fixedpoint_query_from_lvl"] = createExportWrapper("async_Z3_fixedpoint_query_from_lvl");
/** @type {function(...*):?} */
var _async_Z3_polynomial_subresultants = Module["_async_Z3_polynomial_subresultants"] = createExportWrapper("async_Z3_polynomial_subresultants");
/** @type {function(...*):?} */
var _Z3_eval_smtlib2_string = Module["_Z3_eval_smtlib2_string"] = createExportWrapper("Z3_eval_smtlib2_string");
/** @type {function(...*):?} */
var _Z3_simplify = Module["_Z3_simplify"] = createExportWrapper("Z3_simplify");
/** @type {function(...*):?} */
var _Z3_simplify_ex = Module["_Z3_simplify_ex"] = createExportWrapper("Z3_simplify_ex");
/** @type {function(...*):?} */
var _Z3_solver_check = Module["_Z3_solver_check"] = createExportWrapper("Z3_solver_check");
/** @type {function(...*):?} */
var _Z3_solver_check_assumptions = Module["_Z3_solver_check_assumptions"] = createExportWrapper("Z3_solver_check_assumptions");
/** @type {function(...*):?} */
var _Z3_solver_cube = Module["_Z3_solver_cube"] = createExportWrapper("Z3_solver_cube");
/** @type {function(...*):?} */
var _Z3_solver_get_consequences = Module["_Z3_solver_get_consequences"] = createExportWrapper("Z3_solver_get_consequences");
/** @type {function(...*):?} */
var _Z3_tactic_apply = Module["_Z3_tactic_apply"] = createExportWrapper("Z3_tactic_apply");
/** @type {function(...*):?} */
var _Z3_tactic_apply_ex = Module["_Z3_tactic_apply_ex"] = createExportWrapper("Z3_tactic_apply_ex");
/** @type {function(...*):?} */
var _Z3_optimize_check = Module["_Z3_optimize_check"] = createExportWrapper("Z3_optimize_check");
/** @type {function(...*):?} */
var _Z3_algebraic_roots = Module["_Z3_algebraic_roots"] = createExportWrapper("Z3_algebraic_roots");
/** @type {function(...*):?} */
var _Z3_algebraic_eval = Module["_Z3_algebraic_eval"] = createExportWrapper("Z3_algebraic_eval");
/** @type {function(...*):?} */
var _Z3_fixedpoint_query = Module["_Z3_fixedpoint_query"] = createExportWrapper("Z3_fixedpoint_query");
/** @type {function(...*):?} */
var _Z3_fixedpoint_query_relations = Module["_Z3_fixedpoint_query_relations"] = createExportWrapper("Z3_fixedpoint_query_relations");
/** @type {function(...*):?} */
var _Z3_fixedpoint_query_from_lvl = Module["_Z3_fixedpoint_query_from_lvl"] = createExportWrapper("Z3_fixedpoint_query_from_lvl");
/** @type {function(...*):?} */
var _Z3_polynomial_subresultants = Module["_Z3_polynomial_subresultants"] = createExportWrapper("Z3_polynomial_subresultants");
/** @type {function(...*):?} */
var _Z3_mk_simple_solver = Module["_Z3_mk_simple_solver"] = createExportWrapper("Z3_mk_simple_solver");
/** @type {function(...*):?} */
var _Z3_mk_solver = Module["_Z3_mk_solver"] = createExportWrapper("Z3_mk_solver");
/** @type {function(...*):?} */
var _Z3_mk_solver_for_logic = Module["_Z3_mk_solver_for_logic"] = createExportWrapper("Z3_mk_solver_for_logic");
/** @type {function(...*):?} */
var _Z3_mk_solver_from_tactic = Module["_Z3_mk_solver_from_tactic"] = createExportWrapper("Z3_mk_solver_from_tactic");
/** @type {function(...*):?} */
var _Z3_solver_add_simplifier = Module["_Z3_solver_add_simplifier"] = createExportWrapper("Z3_solver_add_simplifier");
/** @type {function(...*):?} */
var _Z3_solver_translate = Module["_Z3_solver_translate"] = createExportWrapper("Z3_solver_translate");
/** @type {function(...*):?} */
var _Z3_solver_import_model_converter = Module["_Z3_solver_import_model_converter"] = createExportWrapper("Z3_solver_import_model_converter");
/** @type {function(...*):?} */
var _Z3_solver_from_string = Module["_Z3_solver_from_string"] = createExportWrapper("Z3_solver_from_string");
/** @type {function(...*):?} */
var _Z3_solver_from_file = Module["_Z3_solver_from_file"] = createExportWrapper("Z3_solver_from_file");
/** @type {function(...*):?} */
var _Z3_solver_get_help = Module["_Z3_solver_get_help"] = createExportWrapper("Z3_solver_get_help");
/** @type {function(...*):?} */
var _Z3_solver_get_param_descrs = Module["_Z3_solver_get_param_descrs"] = createExportWrapper("Z3_solver_get_param_descrs");
/** @type {function(...*):?} */
var _Z3_solver_set_params = Module["_Z3_solver_set_params"] = createExportWrapper("Z3_solver_set_params");
/** @type {function(...*):?} */
var _Z3_solver_inc_ref = Module["_Z3_solver_inc_ref"] = createExportWrapper("Z3_solver_inc_ref");
/** @type {function(...*):?} */
var _Z3_solver_dec_ref = Module["_Z3_solver_dec_ref"] = createExportWrapper("Z3_solver_dec_ref");
/** @type {function(...*):?} */
var _Z3_solver_push = Module["_Z3_solver_push"] = createExportWrapper("Z3_solver_push");
/** @type {function(...*):?} */
var _Z3_solver_interrupt = Module["_Z3_solver_interrupt"] = createExportWrapper("Z3_solver_interrupt");
/** @type {function(...*):?} */
var _Z3_solver_pop = Module["_Z3_solver_pop"] = createExportWrapper("Z3_solver_pop");
/** @type {function(...*):?} */
var _Z3_solver_reset = Module["_Z3_solver_reset"] = createExportWrapper("Z3_solver_reset");
/** @type {function(...*):?} */
var _Z3_solver_get_num_scopes = Module["_Z3_solver_get_num_scopes"] = createExportWrapper("Z3_solver_get_num_scopes");
/** @type {function(...*):?} */
var _Z3_solver_assert = Module["_Z3_solver_assert"] = createExportWrapper("Z3_solver_assert");
/** @type {function(...*):?} */
var _Z3_solver_assert_and_track = Module["_Z3_solver_assert_and_track"] = createExportWrapper("Z3_solver_assert_and_track");
/** @type {function(...*):?} */
var _Z3_solver_get_assertions = Module["_Z3_solver_get_assertions"] = createExportWrapper("Z3_solver_get_assertions");
/** @type {function(...*):?} */
var _Z3_solver_get_units = Module["_Z3_solver_get_units"] = createExportWrapper("Z3_solver_get_units");
/** @type {function(...*):?} */
var _Z3_solver_get_non_units = Module["_Z3_solver_get_non_units"] = createExportWrapper("Z3_solver_get_non_units");
/** @type {function(...*):?} */
var _Z3_solver_get_levels = Module["_Z3_solver_get_levels"] = createExportWrapper("Z3_solver_get_levels");
/** @type {function(...*):?} */
var _Z3_solver_get_trail = Module["_Z3_solver_get_trail"] = createExportWrapper("Z3_solver_get_trail");
/** @type {function(...*):?} */
var _pthread_self = Module["_pthread_self"] = createExportWrapper("pthread_self");
/** @type {function(...*):?} */
var _Z3_ast_vector_size = Module["_Z3_ast_vector_size"] = createExportWrapper("Z3_ast_vector_size");
/** @type {function(...*):?} */
var _Z3_ast_vector_get = Module["_Z3_ast_vector_get"] = createExportWrapper("Z3_ast_vector_get");
/** @type {function(...*):?} */
var _Z3_solver_get_model = Module["_Z3_solver_get_model"] = createExportWrapper("Z3_solver_get_model");
/** @type {function(...*):?} */
var _Z3_solver_get_proof = Module["_Z3_solver_get_proof"] = createExportWrapper("Z3_solver_get_proof");
/** @type {function(...*):?} */
var _Z3_solver_get_unsat_core = Module["_Z3_solver_get_unsat_core"] = createExportWrapper("Z3_solver_get_unsat_core");
/** @type {function(...*):?} */
var _Z3_solver_get_reason_unknown = Module["_Z3_solver_get_reason_unknown"] = createExportWrapper("Z3_solver_get_reason_unknown");
/** @type {function(...*):?} */
var _Z3_solver_get_statistics = Module["_Z3_solver_get_statistics"] = createExportWrapper("Z3_solver_get_statistics");
/** @type {function(...*):?} */
var _Z3_solver_to_string = Module["_Z3_solver_to_string"] = createExportWrapper("Z3_solver_to_string");
/** @type {function(...*):?} */
var _Z3_solver_to_dimacs_string = Module["_Z3_solver_to_dimacs_string"] = createExportWrapper("Z3_solver_to_dimacs_string");
/** @type {function(...*):?} */
var _Z3_get_implied_equalities = Module["_Z3_get_implied_equalities"] = createExportWrapper("Z3_get_implied_equalities");
/** @type {function(...*):?} */
var _Z3_solver_congruence_root = Module["_Z3_solver_congruence_root"] = createExportWrapper("Z3_solver_congruence_root");
/** @type {function(...*):?} */
var _Z3_solver_congruence_next = Module["_Z3_solver_congruence_next"] = createExportWrapper("Z3_solver_congruence_next");
/** @type {function(...*):?} */
var _Z3_solver_register_on_clause = Module["_Z3_solver_register_on_clause"] = createExportWrapper("Z3_solver_register_on_clause");
/** @type {function(...*):?} */
var _Z3_solver_propagate_init = Module["_Z3_solver_propagate_init"] = createExportWrapper("Z3_solver_propagate_init");
/** @type {function(...*):?} */
var _Z3_solver_propagate_fixed = Module["_Z3_solver_propagate_fixed"] = createExportWrapper("Z3_solver_propagate_fixed");
/** @type {function(...*):?} */
var _Z3_solver_propagate_final = Module["_Z3_solver_propagate_final"] = createExportWrapper("Z3_solver_propagate_final");
/** @type {function(...*):?} */
var _Z3_solver_propagate_eq = Module["_Z3_solver_propagate_eq"] = createExportWrapper("Z3_solver_propagate_eq");
/** @type {function(...*):?} */
var _Z3_solver_propagate_diseq = Module["_Z3_solver_propagate_diseq"] = createExportWrapper("Z3_solver_propagate_diseq");
/** @type {function(...*):?} */
var _Z3_solver_propagate_register = Module["_Z3_solver_propagate_register"] = createExportWrapper("Z3_solver_propagate_register");
/** @type {function(...*):?} */
var _Z3_solver_propagate_register_cb = Module["_Z3_solver_propagate_register_cb"] = createExportWrapper("Z3_solver_propagate_register_cb");
/** @type {function(...*):?} */
var _Z3_solver_propagate_consequence = Module["_Z3_solver_propagate_consequence"] = createExportWrapper("Z3_solver_propagate_consequence");
/** @type {function(...*):?} */
var _Z3_solver_propagate_created = Module["_Z3_solver_propagate_created"] = createExportWrapper("Z3_solver_propagate_created");
/** @type {function(...*):?} */
var _Z3_solver_propagate_decide = Module["_Z3_solver_propagate_decide"] = createExportWrapper("Z3_solver_propagate_decide");
/** @type {function(...*):?} */
var _Z3_solver_next_split = Module["_Z3_solver_next_split"] = createExportWrapper("Z3_solver_next_split");
/** @type {function(...*):?} */
var _Z3_solver_propagate_declare = Module["_Z3_solver_propagate_declare"] = createExportWrapper("Z3_solver_propagate_declare");
/** @type {function(...*):?} */
var _Z3_mk_tactic = Module["_Z3_mk_tactic"] = createExportWrapper("Z3_mk_tactic");
/** @type {function(...*):?} */
var _Z3_tactic_inc_ref = Module["_Z3_tactic_inc_ref"] = createExportWrapper("Z3_tactic_inc_ref");
/** @type {function(...*):?} */
var _Z3_tactic_dec_ref = Module["_Z3_tactic_dec_ref"] = createExportWrapper("Z3_tactic_dec_ref");
/** @type {function(...*):?} */
var _Z3_mk_probe = Module["_Z3_mk_probe"] = createExportWrapper("Z3_mk_probe");
/** @type {function(...*):?} */
var _Z3_probe_inc_ref = Module["_Z3_probe_inc_ref"] = createExportWrapper("Z3_probe_inc_ref");
/** @type {function(...*):?} */
var _Z3_probe_dec_ref = Module["_Z3_probe_dec_ref"] = createExportWrapper("Z3_probe_dec_ref");
/** @type {function(...*):?} */
var _Z3_tactic_and_then = Module["_Z3_tactic_and_then"] = createExportWrapper("Z3_tactic_and_then");
/** @type {function(...*):?} */
var _Z3_tactic_or_else = Module["_Z3_tactic_or_else"] = createExportWrapper("Z3_tactic_or_else");
/** @type {function(...*):?} */
var _Z3_tactic_par_or = Module["_Z3_tactic_par_or"] = createExportWrapper("Z3_tactic_par_or");
/** @type {function(...*):?} */
var _Z3_tactic_par_and_then = Module["_Z3_tactic_par_and_then"] = createExportWrapper("Z3_tactic_par_and_then");
/** @type {function(...*):?} */
var _Z3_tactic_try_for = Module["_Z3_tactic_try_for"] = createExportWrapper("Z3_tactic_try_for");
/** @type {function(...*):?} */
var _Z3_tactic_when = Module["_Z3_tactic_when"] = createExportWrapper("Z3_tactic_when");
/** @type {function(...*):?} */
var _Z3_tactic_cond = Module["_Z3_tactic_cond"] = createExportWrapper("Z3_tactic_cond");
/** @type {function(...*):?} */
var _Z3_tactic_repeat = Module["_Z3_tactic_repeat"] = createExportWrapper("Z3_tactic_repeat");
/** @type {function(...*):?} */
var _Z3_tactic_skip = Module["_Z3_tactic_skip"] = createExportWrapper("Z3_tactic_skip");
/** @type {function(...*):?} */
var _Z3_tactic_fail = Module["_Z3_tactic_fail"] = createExportWrapper("Z3_tactic_fail");
/** @type {function(...*):?} */
var _Z3_tactic_fail_if = Module["_Z3_tactic_fail_if"] = createExportWrapper("Z3_tactic_fail_if");
/** @type {function(...*):?} */
var _Z3_tactic_fail_if_not_decided = Module["_Z3_tactic_fail_if_not_decided"] = createExportWrapper("Z3_tactic_fail_if_not_decided");
/** @type {function(...*):?} */
var _Z3_tactic_using_params = Module["_Z3_tactic_using_params"] = createExportWrapper("Z3_tactic_using_params");
/** @type {function(...*):?} */
var _Z3_probe_const = Module["_Z3_probe_const"] = createExportWrapper("Z3_probe_const");
/** @type {function(...*):?} */
var _Z3_probe_lt = Module["_Z3_probe_lt"] = createExportWrapper("Z3_probe_lt");
/** @type {function(...*):?} */
var _Z3_probe_gt = Module["_Z3_probe_gt"] = createExportWrapper("Z3_probe_gt");
/** @type {function(...*):?} */
var _Z3_probe_le = Module["_Z3_probe_le"] = createExportWrapper("Z3_probe_le");
/** @type {function(...*):?} */
var _Z3_probe_ge = Module["_Z3_probe_ge"] = createExportWrapper("Z3_probe_ge");
/** @type {function(...*):?} */
var _Z3_probe_eq = Module["_Z3_probe_eq"] = createExportWrapper("Z3_probe_eq");
/** @type {function(...*):?} */
var _Z3_probe_and = Module["_Z3_probe_and"] = createExportWrapper("Z3_probe_and");
/** @type {function(...*):?} */
var _Z3_probe_or = Module["_Z3_probe_or"] = createExportWrapper("Z3_probe_or");
/** @type {function(...*):?} */
var _Z3_probe_not = Module["_Z3_probe_not"] = createExportWrapper("Z3_probe_not");
/** @type {function(...*):?} */
var _Z3_get_num_tactics = Module["_Z3_get_num_tactics"] = createExportWrapper("Z3_get_num_tactics");
/** @type {function(...*):?} */
var _Z3_get_tactic_name = Module["_Z3_get_tactic_name"] = createExportWrapper("Z3_get_tactic_name");
/** @type {function(...*):?} */
var _Z3_get_num_probes = Module["_Z3_get_num_probes"] = createExportWrapper("Z3_get_num_probes");
/** @type {function(...*):?} */
var _Z3_get_probe_name = Module["_Z3_get_probe_name"] = createExportWrapper("Z3_get_probe_name");
/** @type {function(...*):?} */
var _Z3_tactic_get_help = Module["_Z3_tactic_get_help"] = createExportWrapper("Z3_tactic_get_help");
/** @type {function(...*):?} */
var _Z3_tactic_get_param_descrs = Module["_Z3_tactic_get_param_descrs"] = createExportWrapper("Z3_tactic_get_param_descrs");
/** @type {function(...*):?} */
var _Z3_tactic_get_descr = Module["_Z3_tactic_get_descr"] = createExportWrapper("Z3_tactic_get_descr");
/** @type {function(...*):?} */
var _Z3_probe_get_descr = Module["_Z3_probe_get_descr"] = createExportWrapper("Z3_probe_get_descr");
/** @type {function(...*):?} */
var _Z3_probe_apply = Module["_Z3_probe_apply"] = createExportWrapper("Z3_probe_apply");
/** @type {function(...*):?} */
var _Z3_apply_result_inc_ref = Module["_Z3_apply_result_inc_ref"] = createExportWrapper("Z3_apply_result_inc_ref");
/** @type {function(...*):?} */
var _Z3_apply_result_dec_ref = Module["_Z3_apply_result_dec_ref"] = createExportWrapper("Z3_apply_result_dec_ref");
/** @type {function(...*):?} */
var _Z3_apply_result_to_string = Module["_Z3_apply_result_to_string"] = createExportWrapper("Z3_apply_result_to_string");
/** @type {function(...*):?} */
var _Z3_apply_result_get_num_subgoals = Module["_Z3_apply_result_get_num_subgoals"] = createExportWrapper("Z3_apply_result_get_num_subgoals");
/** @type {function(...*):?} */
var _Z3_apply_result_get_subgoal = Module["_Z3_apply_result_get_subgoal"] = createExportWrapper("Z3_apply_result_get_subgoal");
/** @type {function(...*):?} */
var _Z3_mk_simplifier = Module["_Z3_mk_simplifier"] = createExportWrapper("Z3_mk_simplifier");
/** @type {function(...*):?} */
var _Z3_simplifier_inc_ref = Module["_Z3_simplifier_inc_ref"] = createExportWrapper("Z3_simplifier_inc_ref");
/** @type {function(...*):?} */
var _Z3_simplifier_dec_ref = Module["_Z3_simplifier_dec_ref"] = createExportWrapper("Z3_simplifier_dec_ref");
/** @type {function(...*):?} */
var _Z3_get_num_simplifiers = Module["_Z3_get_num_simplifiers"] = createExportWrapper("Z3_get_num_simplifiers");
/** @type {function(...*):?} */
var _Z3_get_simplifier_name = Module["_Z3_get_simplifier_name"] = createExportWrapper("Z3_get_simplifier_name");
/** @type {function(...*):?} */
var _Z3_simplifier_and_then = Module["_Z3_simplifier_and_then"] = createExportWrapper("Z3_simplifier_and_then");
/** @type {function(...*):?} */
var _Z3_simplifier_using_params = Module["_Z3_simplifier_using_params"] = createExportWrapper("Z3_simplifier_using_params");
/** @type {function(...*):?} */
var _Z3_simplifier_get_help = Module["_Z3_simplifier_get_help"] = createExportWrapper("Z3_simplifier_get_help");
/** @type {function(...*):?} */
var _Z3_simplifier_get_param_descrs = Module["_Z3_simplifier_get_param_descrs"] = createExportWrapper("Z3_simplifier_get_param_descrs");
/** @type {function(...*):?} */
var _Z3_simplifier_get_descr = Module["_Z3_simplifier_get_descr"] = createExportWrapper("Z3_simplifier_get_descr");
/** @type {function(...*):?} */
var _Z3_mk_ast_map = Module["_Z3_mk_ast_map"] = createExportWrapper("Z3_mk_ast_map");
/** @type {function(...*):?} */
var _Z3_ast_map_inc_ref = Module["_Z3_ast_map_inc_ref"] = createExportWrapper("Z3_ast_map_inc_ref");
/** @type {function(...*):?} */
var _Z3_ast_map_dec_ref = Module["_Z3_ast_map_dec_ref"] = createExportWrapper("Z3_ast_map_dec_ref");
/** @type {function(...*):?} */
var _Z3_ast_map_contains = Module["_Z3_ast_map_contains"] = createExportWrapper("Z3_ast_map_contains");
/** @type {function(...*):?} */
var _Z3_ast_map_find = Module["_Z3_ast_map_find"] = createExportWrapper("Z3_ast_map_find");
/** @type {function(...*):?} */
var _Z3_ast_map_insert = Module["_Z3_ast_map_insert"] = createExportWrapper("Z3_ast_map_insert");
/** @type {function(...*):?} */
var _Z3_ast_map_reset = Module["_Z3_ast_map_reset"] = createExportWrapper("Z3_ast_map_reset");
/** @type {function(...*):?} */
var _Z3_ast_map_erase = Module["_Z3_ast_map_erase"] = createExportWrapper("Z3_ast_map_erase");
/** @type {function(...*):?} */
var _Z3_ast_map_size = Module["_Z3_ast_map_size"] = createExportWrapper("Z3_ast_map_size");
/** @type {function(...*):?} */
var _Z3_ast_map_keys = Module["_Z3_ast_map_keys"] = createExportWrapper("Z3_ast_map_keys");
/** @type {function(...*):?} */
var _Z3_ast_map_to_string = Module["_Z3_ast_map_to_string"] = createExportWrapper("Z3_ast_map_to_string");
/** @type {function(...*):?} */
var _Z3_mk_context = Module["_Z3_mk_context"] = createExportWrapper("Z3_mk_context");
/** @type {function(...*):?} */
var _Z3_mk_context_rc = Module["_Z3_mk_context_rc"] = createExportWrapper("Z3_mk_context_rc");
/** @type {function(...*):?} */
var _Z3_del_context = Module["_Z3_del_context"] = createExportWrapper("Z3_del_context");
/** @type {function(...*):?} */
var _Z3_interrupt = Module["_Z3_interrupt"] = createExportWrapper("Z3_interrupt");
/** @type {function(...*):?} */
var _Z3_enable_concurrent_dec_ref = Module["_Z3_enable_concurrent_dec_ref"] = createExportWrapper("Z3_enable_concurrent_dec_ref");
/** @type {function(...*):?} */
var _Z3_toggle_warning_messages = Module["_Z3_toggle_warning_messages"] = createExportWrapper("Z3_toggle_warning_messages");
/** @type {function(...*):?} */
var _Z3_inc_ref = Module["_Z3_inc_ref"] = createExportWrapper("Z3_inc_ref");
/** @type {function(...*):?} */
var _Z3_dec_ref = Module["_Z3_dec_ref"] = createExportWrapper("Z3_dec_ref");
/** @type {function(...*):?} */
var _Z3_get_version = Module["_Z3_get_version"] = createExportWrapper("Z3_get_version");
/** @type {function(...*):?} */
var _Z3_get_full_version = Module["_Z3_get_full_version"] = createExportWrapper("Z3_get_full_version");
/** @type {function(...*):?} */
var _Z3_enable_trace = Module["_Z3_enable_trace"] = createExportWrapper("Z3_enable_trace");
/** @type {function(...*):?} */
var _Z3_disable_trace = Module["_Z3_disable_trace"] = createExportWrapper("Z3_disable_trace");
/** @type {function(...*):?} */
var _Z3_reset_memory = Module["_Z3_reset_memory"] = createExportWrapper("Z3_reset_memory");
/** @type {function(...*):?} */
var _Z3_finalize_memory = Module["_Z3_finalize_memory"] = createExportWrapper("Z3_finalize_memory");
/** @type {function(...*):?} */
var _Z3_get_error_code = Module["_Z3_get_error_code"] = createExportWrapper("Z3_get_error_code");
/** @type {function(...*):?} */
var _Z3_set_error = Module["_Z3_set_error"] = createExportWrapper("Z3_set_error");
/** @type {function(...*):?} */
var _Z3_set_ast_print_mode = Module["_Z3_set_ast_print_mode"] = createExportWrapper("Z3_set_ast_print_mode");
/** @type {function(...*):?} */
var _Z3_mk_atmost = Module["_Z3_mk_atmost"] = createExportWrapper("Z3_mk_atmost");
/** @type {function(...*):?} */
var _Z3_mk_atleast = Module["_Z3_mk_atleast"] = createExportWrapper("Z3_mk_atleast");
/** @type {function(...*):?} */
var _Z3_mk_pble = Module["_Z3_mk_pble"] = createExportWrapper("Z3_mk_pble");
/** @type {function(...*):?} */
var _Z3_mk_pbge = Module["_Z3_mk_pbge"] = createExportWrapper("Z3_mk_pbge");
/** @type {function(...*):?} */
var _Z3_mk_pbeq = Module["_Z3_mk_pbeq"] = createExportWrapper("Z3_mk_pbeq");
/** @type {function(...*):?} */
var _Z3_global_param_set = Module["_Z3_global_param_set"] = createExportWrapper("Z3_global_param_set");
/** @type {function(...*):?} */
var _Z3_global_param_reset_all = Module["_Z3_global_param_reset_all"] = createExportWrapper("Z3_global_param_reset_all");
/** @type {function(...*):?} */
var _Z3_global_param_get = Module["_Z3_global_param_get"] = createExportWrapper("Z3_global_param_get");
/** @type {function(...*):?} */
var _Z3_get_global_param_descrs = Module["_Z3_get_global_param_descrs"] = createExportWrapper("Z3_get_global_param_descrs");
/** @type {function(...*):?} */
var _Z3_mk_config = Module["_Z3_mk_config"] = createExportWrapper("Z3_mk_config");
/** @type {function(...*):?} */
var _Z3_del_config = Module["_Z3_del_config"] = createExportWrapper("Z3_del_config");
/** @type {function(...*):?} */
var _Z3_set_param_value = Module["_Z3_set_param_value"] = createExportWrapper("Z3_set_param_value");
/** @type {function(...*):?} */
var _Z3_update_param_value = Module["_Z3_update_param_value"] = createExportWrapper("Z3_update_param_value");
/** @type {function(...*):?} */
var _Z3_mk_seq_sort = Module["_Z3_mk_seq_sort"] = createExportWrapper("Z3_mk_seq_sort");
/** @type {function(...*):?} */
var _Z3_mk_re_sort = Module["_Z3_mk_re_sort"] = createExportWrapper("Z3_mk_re_sort");
/** @type {function(...*):?} */
var _Z3_mk_string = Module["_Z3_mk_string"] = createExportWrapper("Z3_mk_string");
/** @type {function(...*):?} */
var _Z3_mk_lstring = Module["_Z3_mk_lstring"] = createExportWrapper("Z3_mk_lstring");
/** @type {function(...*):?} */
var _Z3_mk_u32string = Module["_Z3_mk_u32string"] = createExportWrapper("Z3_mk_u32string");
/** @type {function(...*):?} */
var _Z3_mk_char = Module["_Z3_mk_char"] = createExportWrapper("Z3_mk_char");
/** @type {function(...*):?} */
var _Z3_mk_string_sort = Module["_Z3_mk_string_sort"] = createExportWrapper("Z3_mk_string_sort");
/** @type {function(...*):?} */
var _Z3_mk_char_sort = Module["_Z3_mk_char_sort"] = createExportWrapper("Z3_mk_char_sort");
/** @type {function(...*):?} */
var _Z3_is_seq_sort = Module["_Z3_is_seq_sort"] = createExportWrapper("Z3_is_seq_sort");
/** @type {function(...*):?} */
var _Z3_is_re_sort = Module["_Z3_is_re_sort"] = createExportWrapper("Z3_is_re_sort");
/** @type {function(...*):?} */
var _Z3_get_seq_sort_basis = Module["_Z3_get_seq_sort_basis"] = createExportWrapper("Z3_get_seq_sort_basis");
/** @type {function(...*):?} */
var _Z3_get_re_sort_basis = Module["_Z3_get_re_sort_basis"] = createExportWrapper("Z3_get_re_sort_basis");
/** @type {function(...*):?} */
var _Z3_is_char_sort = Module["_Z3_is_char_sort"] = createExportWrapper("Z3_is_char_sort");
/** @type {function(...*):?} */
var _Z3_is_string_sort = Module["_Z3_is_string_sort"] = createExportWrapper("Z3_is_string_sort");
/** @type {function(...*):?} */
var _Z3_is_string = Module["_Z3_is_string"] = createExportWrapper("Z3_is_string");
/** @type {function(...*):?} */
var _Z3_get_string = Module["_Z3_get_string"] = createExportWrapper("Z3_get_string");
/** @type {function(...*):?} */
var _Z3_get_lstring = Module["_Z3_get_lstring"] = createExportWrapper("Z3_get_lstring");
/** @type {function(...*):?} */
var _Z3_get_string_length = Module["_Z3_get_string_length"] = createExportWrapper("Z3_get_string_length");
/** @type {function(...*):?} */
var _Z3_get_string_contents = Module["_Z3_get_string_contents"] = createExportWrapper("Z3_get_string_contents");
/** @type {function(...*):?} */
var _Z3_mk_seq_empty = Module["_Z3_mk_seq_empty"] = createExportWrapper("Z3_mk_seq_empty");
/** @type {function(...*):?} */
var _Z3_mk_seq_unit = Module["_Z3_mk_seq_unit"] = createExportWrapper("Z3_mk_seq_unit");
/** @type {function(...*):?} */
var _Z3_mk_seq_concat = Module["_Z3_mk_seq_concat"] = createExportWrapper("Z3_mk_seq_concat");
/** @type {function(...*):?} */
var _Z3_mk_seq_prefix = Module["_Z3_mk_seq_prefix"] = createExportWrapper("Z3_mk_seq_prefix");
/** @type {function(...*):?} */
var _Z3_mk_seq_suffix = Module["_Z3_mk_seq_suffix"] = createExportWrapper("Z3_mk_seq_suffix");
/** @type {function(...*):?} */
var _Z3_mk_seq_contains = Module["_Z3_mk_seq_contains"] = createExportWrapper("Z3_mk_seq_contains");
/** @type {function(...*):?} */
var _Z3_mk_str_lt = Module["_Z3_mk_str_lt"] = createExportWrapper("Z3_mk_str_lt");
/** @type {function(...*):?} */
var _Z3_mk_str_le = Module["_Z3_mk_str_le"] = createExportWrapper("Z3_mk_str_le");
/** @type {function(...*):?} */
var _Z3_mk_string_to_code = Module["_Z3_mk_string_to_code"] = createExportWrapper("Z3_mk_string_to_code");
/** @type {function(...*):?} */
var _Z3_mk_string_from_code = Module["_Z3_mk_string_from_code"] = createExportWrapper("Z3_mk_string_from_code");
/** @type {function(...*):?} */
var _Z3_mk_seq_extract = Module["_Z3_mk_seq_extract"] = createExportWrapper("Z3_mk_seq_extract");
/** @type {function(...*):?} */
var _Z3_mk_seq_replace = Module["_Z3_mk_seq_replace"] = createExportWrapper("Z3_mk_seq_replace");
/** @type {function(...*):?} */
var _Z3_mk_seq_at = Module["_Z3_mk_seq_at"] = createExportWrapper("Z3_mk_seq_at");
/** @type {function(...*):?} */
var _Z3_mk_seq_nth = Module["_Z3_mk_seq_nth"] = createExportWrapper("Z3_mk_seq_nth");
/** @type {function(...*):?} */
var _Z3_mk_seq_length = Module["_Z3_mk_seq_length"] = createExportWrapper("Z3_mk_seq_length");
/** @type {function(...*):?} */
var _Z3_mk_seq_index = Module["_Z3_mk_seq_index"] = createExportWrapper("Z3_mk_seq_index");
/** @type {function(...*):?} */
var _Z3_mk_seq_last_index = Module["_Z3_mk_seq_last_index"] = createExportWrapper("Z3_mk_seq_last_index");
/** @type {function(...*):?} */
var _Z3_mk_seq_to_re = Module["_Z3_mk_seq_to_re"] = createExportWrapper("Z3_mk_seq_to_re");
/** @type {function(...*):?} */
var _Z3_mk_seq_in_re = Module["_Z3_mk_seq_in_re"] = createExportWrapper("Z3_mk_seq_in_re");
/** @type {function(...*):?} */
var _Z3_mk_int_to_str = Module["_Z3_mk_int_to_str"] = createExportWrapper("Z3_mk_int_to_str");
/** @type {function(...*):?} */
var _Z3_mk_str_to_int = Module["_Z3_mk_str_to_int"] = createExportWrapper("Z3_mk_str_to_int");
/** @type {function(...*):?} */
var _Z3_mk_ubv_to_str = Module["_Z3_mk_ubv_to_str"] = createExportWrapper("Z3_mk_ubv_to_str");
/** @type {function(...*):?} */
var _Z3_mk_sbv_to_str = Module["_Z3_mk_sbv_to_str"] = createExportWrapper("Z3_mk_sbv_to_str");
/** @type {function(...*):?} */
var _Z3_mk_re_loop = Module["_Z3_mk_re_loop"] = createExportWrapper("Z3_mk_re_loop");
/** @type {function(...*):?} */
var _Z3_mk_re_power = Module["_Z3_mk_re_power"] = createExportWrapper("Z3_mk_re_power");
/** @type {function(...*):?} */
var _Z3_mk_re_plus = Module["_Z3_mk_re_plus"] = createExportWrapper("Z3_mk_re_plus");
/** @type {function(...*):?} */
var _Z3_mk_re_star = Module["_Z3_mk_re_star"] = createExportWrapper("Z3_mk_re_star");
/** @type {function(...*):?} */
var _Z3_mk_re_option = Module["_Z3_mk_re_option"] = createExportWrapper("Z3_mk_re_option");
/** @type {function(...*):?} */
var _Z3_mk_re_complement = Module["_Z3_mk_re_complement"] = createExportWrapper("Z3_mk_re_complement");
/** @type {function(...*):?} */
var _Z3_mk_re_diff = Module["_Z3_mk_re_diff"] = createExportWrapper("Z3_mk_re_diff");
/** @type {function(...*):?} */
var _Z3_mk_re_union = Module["_Z3_mk_re_union"] = createExportWrapper("Z3_mk_re_union");
/** @type {function(...*):?} */
var _Z3_mk_re_intersect = Module["_Z3_mk_re_intersect"] = createExportWrapper("Z3_mk_re_intersect");
/** @type {function(...*):?} */
var _Z3_mk_re_concat = Module["_Z3_mk_re_concat"] = createExportWrapper("Z3_mk_re_concat");
/** @type {function(...*):?} */
var _Z3_mk_re_range = Module["_Z3_mk_re_range"] = createExportWrapper("Z3_mk_re_range");
/** @type {function(...*):?} */
var _Z3_mk_re_allchar = Module["_Z3_mk_re_allchar"] = createExportWrapper("Z3_mk_re_allchar");
/** @type {function(...*):?} */
var _Z3_mk_re_empty = Module["_Z3_mk_re_empty"] = createExportWrapper("Z3_mk_re_empty");
/** @type {function(...*):?} */
var _Z3_mk_re_full = Module["_Z3_mk_re_full"] = createExportWrapper("Z3_mk_re_full");
/** @type {function(...*):?} */
var _Z3_mk_char_le = Module["_Z3_mk_char_le"] = createExportWrapper("Z3_mk_char_le");
/** @type {function(...*):?} */
var _Z3_mk_char_to_int = Module["_Z3_mk_char_to_int"] = createExportWrapper("Z3_mk_char_to_int");
/** @type {function(...*):?} */
var _Z3_mk_char_to_bv = Module["_Z3_mk_char_to_bv"] = createExportWrapper("Z3_mk_char_to_bv");
/** @type {function(...*):?} */
var _Z3_mk_char_from_bv = Module["_Z3_mk_char_from_bv"] = createExportWrapper("Z3_mk_char_from_bv");
/** @type {function(...*):?} */
var _Z3_mk_char_is_digit = Module["_Z3_mk_char_is_digit"] = createExportWrapper("Z3_mk_char_is_digit");
/** @type {function(...*):?} */
var _Z3_rcf_del = Module["_Z3_rcf_del"] = createExportWrapper("Z3_rcf_del");
/** @type {function(...*):?} */
var _Z3_rcf_mk_rational = Module["_Z3_rcf_mk_rational"] = createExportWrapper("Z3_rcf_mk_rational");
/** @type {function(...*):?} */
var _Z3_rcf_mk_small_int = Module["_Z3_rcf_mk_small_int"] = createExportWrapper("Z3_rcf_mk_small_int");
/** @type {function(...*):?} */
var _Z3_rcf_mk_pi = Module["_Z3_rcf_mk_pi"] = createExportWrapper("Z3_rcf_mk_pi");
/** @type {function(...*):?} */
var _Z3_rcf_mk_e = Module["_Z3_rcf_mk_e"] = createExportWrapper("Z3_rcf_mk_e");
/** @type {function(...*):?} */
var _Z3_rcf_mk_infinitesimal = Module["_Z3_rcf_mk_infinitesimal"] = createExportWrapper("Z3_rcf_mk_infinitesimal");
/** @type {function(...*):?} */
var _Z3_rcf_mk_roots = Module["_Z3_rcf_mk_roots"] = createExportWrapper("Z3_rcf_mk_roots");
/** @type {function(...*):?} */
var _Z3_rcf_add = Module["_Z3_rcf_add"] = createExportWrapper("Z3_rcf_add");
/** @type {function(...*):?} */
var _Z3_rcf_sub = Module["_Z3_rcf_sub"] = createExportWrapper("Z3_rcf_sub");
/** @type {function(...*):?} */
var _Z3_rcf_mul = Module["_Z3_rcf_mul"] = createExportWrapper("Z3_rcf_mul");
/** @type {function(...*):?} */
var _Z3_rcf_div = Module["_Z3_rcf_div"] = createExportWrapper("Z3_rcf_div");
/** @type {function(...*):?} */
var _Z3_rcf_neg = Module["_Z3_rcf_neg"] = createExportWrapper("Z3_rcf_neg");
/** @type {function(...*):?} */
var _Z3_rcf_inv = Module["_Z3_rcf_inv"] = createExportWrapper("Z3_rcf_inv");
/** @type {function(...*):?} */
var _Z3_rcf_power = Module["_Z3_rcf_power"] = createExportWrapper("Z3_rcf_power");
/** @type {function(...*):?} */
var _Z3_rcf_lt = Module["_Z3_rcf_lt"] = createExportWrapper("Z3_rcf_lt");
/** @type {function(...*):?} */
var _Z3_rcf_gt = Module["_Z3_rcf_gt"] = createExportWrapper("Z3_rcf_gt");
/** @type {function(...*):?} */
var _Z3_rcf_le = Module["_Z3_rcf_le"] = createExportWrapper("Z3_rcf_le");
/** @type {function(...*):?} */
var _Z3_rcf_ge = Module["_Z3_rcf_ge"] = createExportWrapper("Z3_rcf_ge");
/** @type {function(...*):?} */
var _Z3_rcf_eq = Module["_Z3_rcf_eq"] = createExportWrapper("Z3_rcf_eq");
/** @type {function(...*):?} */
var _Z3_rcf_neq = Module["_Z3_rcf_neq"] = createExportWrapper("Z3_rcf_neq");
/** @type {function(...*):?} */
var _Z3_rcf_num_to_string = Module["_Z3_rcf_num_to_string"] = createExportWrapper("Z3_rcf_num_to_string");
/** @type {function(...*):?} */
var _Z3_rcf_num_to_decimal_string = Module["_Z3_rcf_num_to_decimal_string"] = createExportWrapper("Z3_rcf_num_to_decimal_string");
/** @type {function(...*):?} */
var _Z3_rcf_get_numerator_denominator = Module["_Z3_rcf_get_numerator_denominator"] = createExportWrapper("Z3_rcf_get_numerator_denominator");
/** @type {function(...*):?} */
var _Z3_mk_tuple_sort = Module["_Z3_mk_tuple_sort"] = createExportWrapper("Z3_mk_tuple_sort");
/** @type {function(...*):?} */
var _Z3_mk_enumeration_sort = Module["_Z3_mk_enumeration_sort"] = createExportWrapper("Z3_mk_enumeration_sort");
/** @type {function(...*):?} */
var _Z3_mk_list_sort = Module["_Z3_mk_list_sort"] = createExportWrapper("Z3_mk_list_sort");
/** @type {function(...*):?} */
var _Z3_mk_constructor = Module["_Z3_mk_constructor"] = createExportWrapper("Z3_mk_constructor");
/** @type {function(...*):?} */
var _Z3_query_constructor = Module["_Z3_query_constructor"] = createExportWrapper("Z3_query_constructor");
/** @type {function(...*):?} */
var _Z3_del_constructor = Module["_Z3_del_constructor"] = createExportWrapper("Z3_del_constructor");
/** @type {function(...*):?} */
var _Z3_mk_datatype = Module["_Z3_mk_datatype"] = createExportWrapper("Z3_mk_datatype");
/** @type {function(...*):?} */
var _Z3_mk_constructor_list = Module["_Z3_mk_constructor_list"] = createExportWrapper("Z3_mk_constructor_list");
/** @type {function(...*):?} */
var _Z3_del_constructor_list = Module["_Z3_del_constructor_list"] = createExportWrapper("Z3_del_constructor_list");
/** @type {function(...*):?} */
var _Z3_mk_datatype_sort = Module["_Z3_mk_datatype_sort"] = createExportWrapper("Z3_mk_datatype_sort");
/** @type {function(...*):?} */
var _Z3_mk_datatypes = Module["_Z3_mk_datatypes"] = createExportWrapper("Z3_mk_datatypes");
/** @type {function(...*):?} */
var _Z3_get_datatype_sort_num_constructors = Module["_Z3_get_datatype_sort_num_constructors"] = createExportWrapper("Z3_get_datatype_sort_num_constructors");
/** @type {function(...*):?} */
var _Z3_get_datatype_sort_constructor = Module["_Z3_get_datatype_sort_constructor"] = createExportWrapper("Z3_get_datatype_sort_constructor");
/** @type {function(...*):?} */
var _Z3_get_datatype_sort_recognizer = Module["_Z3_get_datatype_sort_recognizer"] = createExportWrapper("Z3_get_datatype_sort_recognizer");
/** @type {function(...*):?} */
var _Z3_get_datatype_sort_constructor_accessor = Module["_Z3_get_datatype_sort_constructor_accessor"] = createExportWrapper("Z3_get_datatype_sort_constructor_accessor");
/** @type {function(...*):?} */
var _Z3_get_tuple_sort_mk_decl = Module["_Z3_get_tuple_sort_mk_decl"] = createExportWrapper("Z3_get_tuple_sort_mk_decl");
/** @type {function(...*):?} */
var _Z3_get_tuple_sort_num_fields = Module["_Z3_get_tuple_sort_num_fields"] = createExportWrapper("Z3_get_tuple_sort_num_fields");
/** @type {function(...*):?} */
var _Z3_get_tuple_sort_field_decl = Module["_Z3_get_tuple_sort_field_decl"] = createExportWrapper("Z3_get_tuple_sort_field_decl");
/** @type {function(...*):?} */
var _Z3_datatype_update_field = Module["_Z3_datatype_update_field"] = createExportWrapper("Z3_datatype_update_field");
/** @type {function(...*):?} */
var _Z3_mk_numeral = Module["_Z3_mk_numeral"] = createExportWrapper("Z3_mk_numeral");
/** @type {function(...*):?} */
var _Z3_mk_int = Module["_Z3_mk_int"] = createExportWrapper("Z3_mk_int");
/** @type {function(...*):?} */
var _Z3_mk_unsigned_int = Module["_Z3_mk_unsigned_int"] = createExportWrapper("Z3_mk_unsigned_int");
/** @type {function(...*):?} */
var _Z3_mk_int64 = Module["_Z3_mk_int64"] = createExportWrapper("Z3_mk_int64");
/** @type {function(...*):?} */
var _Z3_mk_unsigned_int64 = Module["_Z3_mk_unsigned_int64"] = createExportWrapper("Z3_mk_unsigned_int64");
/** @type {function(...*):?} */
var _Z3_is_numeral_ast = Module["_Z3_is_numeral_ast"] = createExportWrapper("Z3_is_numeral_ast");
/** @type {function(...*):?} */
var _Z3_get_numeral_binary_string = Module["_Z3_get_numeral_binary_string"] = createExportWrapper("Z3_get_numeral_binary_string");
/** @type {function(...*):?} */
var _Z3_get_numeral_string = Module["_Z3_get_numeral_string"] = createExportWrapper("Z3_get_numeral_string");
/** @type {function(...*):?} */
var _Z3_get_numeral_double = Module["_Z3_get_numeral_double"] = createExportWrapper("Z3_get_numeral_double");
/** @type {function(...*):?} */
var _Z3_get_numeral_decimal_string = Module["_Z3_get_numeral_decimal_string"] = createExportWrapper("Z3_get_numeral_decimal_string");
/** @type {function(...*):?} */
var _Z3_get_numeral_small = Module["_Z3_get_numeral_small"] = createExportWrapper("Z3_get_numeral_small");
/** @type {function(...*):?} */
var _Z3_get_numeral_int = Module["_Z3_get_numeral_int"] = createExportWrapper("Z3_get_numeral_int");
/** @type {function(...*):?} */
var _Z3_get_numeral_int64 = Module["_Z3_get_numeral_int64"] = createExportWrapper("Z3_get_numeral_int64");
/** @type {function(...*):?} */
var _Z3_get_numeral_uint = Module["_Z3_get_numeral_uint"] = createExportWrapper("Z3_get_numeral_uint");
/** @type {function(...*):?} */
var _Z3_get_numeral_uint64 = Module["_Z3_get_numeral_uint64"] = createExportWrapper("Z3_get_numeral_uint64");
/** @type {function(...*):?} */
var _Z3_get_numeral_rational_int64 = Module["_Z3_get_numeral_rational_int64"] = createExportWrapper("Z3_get_numeral_rational_int64");
/** @type {function(...*):?} */
var _Z3_mk_bv_numeral = Module["_Z3_mk_bv_numeral"] = createExportWrapper("Z3_mk_bv_numeral");
/** @type {function(...*):?} */
var _Z3_algebraic_is_value = Module["_Z3_algebraic_is_value"] = createExportWrapper("Z3_algebraic_is_value");
/** @type {function(...*):?} */
var _Z3_algebraic_is_pos = Module["_Z3_algebraic_is_pos"] = createExportWrapper("Z3_algebraic_is_pos");
/** @type {function(...*):?} */
var _Z3_algebraic_sign = Module["_Z3_algebraic_sign"] = createExportWrapper("Z3_algebraic_sign");
/** @type {function(...*):?} */
var _Z3_algebraic_is_neg = Module["_Z3_algebraic_is_neg"] = createExportWrapper("Z3_algebraic_is_neg");
/** @type {function(...*):?} */
var _Z3_algebraic_is_zero = Module["_Z3_algebraic_is_zero"] = createExportWrapper("Z3_algebraic_is_zero");
/** @type {function(...*):?} */
var _Z3_algebraic_add = Module["_Z3_algebraic_add"] = createExportWrapper("Z3_algebraic_add");
/** @type {function(...*):?} */
var _Z3_algebraic_sub = Module["_Z3_algebraic_sub"] = createExportWrapper("Z3_algebraic_sub");
/** @type {function(...*):?} */
var _Z3_algebraic_mul = Module["_Z3_algebraic_mul"] = createExportWrapper("Z3_algebraic_mul");
/** @type {function(...*):?} */
var _Z3_algebraic_div = Module["_Z3_algebraic_div"] = createExportWrapper("Z3_algebraic_div");
/** @type {function(...*):?} */
var _Z3_algebraic_root = Module["_Z3_algebraic_root"] = createExportWrapper("Z3_algebraic_root");
/** @type {function(...*):?} */
var _Z3_algebraic_power = Module["_Z3_algebraic_power"] = createExportWrapper("Z3_algebraic_power");
/** @type {function(...*):?} */
var _Z3_algebraic_lt = Module["_Z3_algebraic_lt"] = createExportWrapper("Z3_algebraic_lt");
/** @type {function(...*):?} */
var _Z3_algebraic_gt = Module["_Z3_algebraic_gt"] = createExportWrapper("Z3_algebraic_gt");
/** @type {function(...*):?} */
var _Z3_algebraic_le = Module["_Z3_algebraic_le"] = createExportWrapper("Z3_algebraic_le");
/** @type {function(...*):?} */
var _Z3_algebraic_ge = Module["_Z3_algebraic_ge"] = createExportWrapper("Z3_algebraic_ge");
/** @type {function(...*):?} */
var _Z3_algebraic_eq = Module["_Z3_algebraic_eq"] = createExportWrapper("Z3_algebraic_eq");
/** @type {function(...*):?} */
var _Z3_algebraic_neq = Module["_Z3_algebraic_neq"] = createExportWrapper("Z3_algebraic_neq");
/** @type {function(...*):?} */
var _Z3_algebraic_get_poly = Module["_Z3_algebraic_get_poly"] = createExportWrapper("Z3_algebraic_get_poly");
/** @type {function(...*):?} */
var _Z3_algebraic_get_i = Module["_Z3_algebraic_get_i"] = createExportWrapper("Z3_algebraic_get_i");
/** @type {function(...*):?} */
var _Z3_get_relation_arity = Module["_Z3_get_relation_arity"] = createExportWrapper("Z3_get_relation_arity");
/** @type {function(...*):?} */
var _Z3_get_relation_column = Module["_Z3_get_relation_column"] = createExportWrapper("Z3_get_relation_column");
/** @type {function(...*):?} */
var _Z3_mk_finite_domain_sort = Module["_Z3_mk_finite_domain_sort"] = createExportWrapper("Z3_mk_finite_domain_sort");
/** @type {function(...*):?} */
var _Z3_get_finite_domain_sort_size = Module["_Z3_get_finite_domain_sort_size"] = createExportWrapper("Z3_get_finite_domain_sort_size");
/** @type {function(...*):?} */
var _Z3_mk_fixedpoint = Module["_Z3_mk_fixedpoint"] = createExportWrapper("Z3_mk_fixedpoint");
/** @type {function(...*):?} */
var _Z3_fixedpoint_inc_ref = Module["_Z3_fixedpoint_inc_ref"] = createExportWrapper("Z3_fixedpoint_inc_ref");
/** @type {function(...*):?} */
var _Z3_fixedpoint_dec_ref = Module["_Z3_fixedpoint_dec_ref"] = createExportWrapper("Z3_fixedpoint_dec_ref");
/** @type {function(...*):?} */
var _Z3_fixedpoint_assert = Module["_Z3_fixedpoint_assert"] = createExportWrapper("Z3_fixedpoint_assert");
/** @type {function(...*):?} */
var _Z3_fixedpoint_add_rule = Module["_Z3_fixedpoint_add_rule"] = createExportWrapper("Z3_fixedpoint_add_rule");
/** @type {function(...*):?} */
var _Z3_fixedpoint_add_fact = Module["_Z3_fixedpoint_add_fact"] = createExportWrapper("Z3_fixedpoint_add_fact");
/** @type {function(...*):?} */
var _Z3_get_sort_kind = Module["_Z3_get_sort_kind"] = createExportWrapper("Z3_get_sort_kind");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_answer = Module["_Z3_fixedpoint_get_answer"] = createExportWrapper("Z3_fixedpoint_get_answer");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_reason_unknown = Module["_Z3_fixedpoint_get_reason_unknown"] = createExportWrapper("Z3_fixedpoint_get_reason_unknown");
/** @type {function(...*):?} */
var _Z3_fixedpoint_to_string = Module["_Z3_fixedpoint_to_string"] = createExportWrapper("Z3_fixedpoint_to_string");
/** @type {function(...*):?} */
var _Z3_fixedpoint_from_string = Module["_Z3_fixedpoint_from_string"] = createExportWrapper("Z3_fixedpoint_from_string");
/** @type {function(...*):?} */
var _Z3_fixedpoint_from_file = Module["_Z3_fixedpoint_from_file"] = createExportWrapper("Z3_fixedpoint_from_file");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_statistics = Module["_Z3_fixedpoint_get_statistics"] = createExportWrapper("Z3_fixedpoint_get_statistics");
/** @type {function(...*):?} */
var _Z3_fixedpoint_register_relation = Module["_Z3_fixedpoint_register_relation"] = createExportWrapper("Z3_fixedpoint_register_relation");
/** @type {function(...*):?} */
var _Z3_fixedpoint_set_predicate_representation = Module["_Z3_fixedpoint_set_predicate_representation"] = createExportWrapper("Z3_fixedpoint_set_predicate_representation");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_rules = Module["_Z3_fixedpoint_get_rules"] = createExportWrapper("Z3_fixedpoint_get_rules");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_assertions = Module["_Z3_fixedpoint_get_assertions"] = createExportWrapper("Z3_fixedpoint_get_assertions");
/** @type {function(...*):?} */
var _Z3_fixedpoint_update_rule = Module["_Z3_fixedpoint_update_rule"] = createExportWrapper("Z3_fixedpoint_update_rule");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_num_levels = Module["_Z3_fixedpoint_get_num_levels"] = createExportWrapper("Z3_fixedpoint_get_num_levels");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_cover_delta = Module["_Z3_fixedpoint_get_cover_delta"] = createExportWrapper("Z3_fixedpoint_get_cover_delta");
/** @type {function(...*):?} */
var _Z3_fixedpoint_add_cover = Module["_Z3_fixedpoint_add_cover"] = createExportWrapper("Z3_fixedpoint_add_cover");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_help = Module["_Z3_fixedpoint_get_help"] = createExportWrapper("Z3_fixedpoint_get_help");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_param_descrs = Module["_Z3_fixedpoint_get_param_descrs"] = createExportWrapper("Z3_fixedpoint_get_param_descrs");
/** @type {function(...*):?} */
var _Z3_fixedpoint_set_params = Module["_Z3_fixedpoint_set_params"] = createExportWrapper("Z3_fixedpoint_set_params");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_ground_sat_answer = Module["_Z3_fixedpoint_get_ground_sat_answer"] = createExportWrapper("Z3_fixedpoint_get_ground_sat_answer");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_rules_along_trace = Module["_Z3_fixedpoint_get_rules_along_trace"] = createExportWrapper("Z3_fixedpoint_get_rules_along_trace");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_rule_names_along_trace = Module["_Z3_fixedpoint_get_rule_names_along_trace"] = createExportWrapper("Z3_fixedpoint_get_rule_names_along_trace");
/** @type {function(...*):?} */
var _Z3_fixedpoint_add_invariant = Module["_Z3_fixedpoint_add_invariant"] = createExportWrapper("Z3_fixedpoint_add_invariant");
/** @type {function(...*):?} */
var _Z3_fixedpoint_get_reachable = Module["_Z3_fixedpoint_get_reachable"] = createExportWrapper("Z3_fixedpoint_get_reachable");
/** @type {function(...*):?} */
var _Z3_mk_int_symbol = Module["_Z3_mk_int_symbol"] = createExportWrapper("Z3_mk_int_symbol");
/** @type {function(...*):?} */
var _Z3_mk_string_symbol = Module["_Z3_mk_string_symbol"] = createExportWrapper("Z3_mk_string_symbol");
/** @type {function(...*):?} */
var _Z3_is_eq_sort = Module["_Z3_is_eq_sort"] = createExportWrapper("Z3_is_eq_sort");
/** @type {function(...*):?} */
var _Z3_mk_uninterpreted_sort = Module["_Z3_mk_uninterpreted_sort"] = createExportWrapper("Z3_mk_uninterpreted_sort");
/** @type {function(...*):?} */
var _Z3_is_eq_ast = Module["_Z3_is_eq_ast"] = createExportWrapper("Z3_is_eq_ast");
/** @type {function(...*):?} */
var _Z3_is_eq_func_decl = Module["_Z3_is_eq_func_decl"] = createExportWrapper("Z3_is_eq_func_decl");
/** @type {function(...*):?} */
var _Z3_mk_func_decl = Module["_Z3_mk_func_decl"] = createExportWrapper("Z3_mk_func_decl");
/** @type {function(...*):?} */
var _Z3_mk_rec_func_decl = Module["_Z3_mk_rec_func_decl"] = createExportWrapper("Z3_mk_rec_func_decl");
/** @type {function(...*):?} */
var _Z3_add_rec_def = Module["_Z3_add_rec_def"] = createExportWrapper("Z3_add_rec_def");
/** @type {function(...*):?} */
var _Z3_mk_app = Module["_Z3_mk_app"] = createExportWrapper("Z3_mk_app");
/** @type {function(...*):?} */
var _Z3_mk_const = Module["_Z3_mk_const"] = createExportWrapper("Z3_mk_const");
/** @type {function(...*):?} */
var _Z3_mk_fresh_func_decl = Module["_Z3_mk_fresh_func_decl"] = createExportWrapper("Z3_mk_fresh_func_decl");
/** @type {function(...*):?} */
var _Z3_mk_fresh_const = Module["_Z3_mk_fresh_const"] = createExportWrapper("Z3_mk_fresh_const");
/** @type {function(...*):?} */
var _Z3_mk_true = Module["_Z3_mk_true"] = createExportWrapper("Z3_mk_true");
/** @type {function(...*):?} */
var _Z3_mk_false = Module["_Z3_mk_false"] = createExportWrapper("Z3_mk_false");
/** @type {function(...*):?} */
var _Z3_mk_not = Module["_Z3_mk_not"] = createExportWrapper("Z3_mk_not");
/** @type {function(...*):?} */
var _Z3_mk_eq = Module["_Z3_mk_eq"] = createExportWrapper("Z3_mk_eq");
/** @type {function(...*):?} */
var _Z3_mk_distinct = Module["_Z3_mk_distinct"] = createExportWrapper("Z3_mk_distinct");
/** @type {function(...*):?} */
var _Z3_mk_iff = Module["_Z3_mk_iff"] = createExportWrapper("Z3_mk_iff");
/** @type {function(...*):?} */
var _Z3_mk_implies = Module["_Z3_mk_implies"] = createExportWrapper("Z3_mk_implies");
/** @type {function(...*):?} */
var _Z3_mk_xor = Module["_Z3_mk_xor"] = createExportWrapper("Z3_mk_xor");
/** @type {function(...*):?} */
var _Z3_mk_and = Module["_Z3_mk_and"] = createExportWrapper("Z3_mk_and");
/** @type {function(...*):?} */
var _Z3_mk_or = Module["_Z3_mk_or"] = createExportWrapper("Z3_mk_or");
/** @type {function(...*):?} */
var _Z3_mk_ite = Module["_Z3_mk_ite"] = createExportWrapper("Z3_mk_ite");
/** @type {function(...*):?} */
var _Z3_mk_bool_sort = Module["_Z3_mk_bool_sort"] = createExportWrapper("Z3_mk_bool_sort");
/** @type {function(...*):?} */
var _Z3_app_to_ast = Module["_Z3_app_to_ast"] = createExportWrapper("Z3_app_to_ast");
/** @type {function(...*):?} */
var _Z3_sort_to_ast = Module["_Z3_sort_to_ast"] = createExportWrapper("Z3_sort_to_ast");
/** @type {function(...*):?} */
var _Z3_func_decl_to_ast = Module["_Z3_func_decl_to_ast"] = createExportWrapper("Z3_func_decl_to_ast");
/** @type {function(...*):?} */
var _Z3_get_ast_id = Module["_Z3_get_ast_id"] = createExportWrapper("Z3_get_ast_id");
/** @type {function(...*):?} */
var _Z3_get_func_decl_id = Module["_Z3_get_func_decl_id"] = createExportWrapper("Z3_get_func_decl_id");
/** @type {function(...*):?} */
var _Z3_get_sort_id = Module["_Z3_get_sort_id"] = createExportWrapper("Z3_get_sort_id");
/** @type {function(...*):?} */
var _Z3_is_well_sorted = Module["_Z3_is_well_sorted"] = createExportWrapper("Z3_is_well_sorted");
/** @type {function(...*):?} */
var _Z3_get_symbol_kind = Module["_Z3_get_symbol_kind"] = createExportWrapper("Z3_get_symbol_kind");
/** @type {function(...*):?} */
var _Z3_get_symbol_int = Module["_Z3_get_symbol_int"] = createExportWrapper("Z3_get_symbol_int");
/** @type {function(...*):?} */
var _Z3_get_symbol_string = Module["_Z3_get_symbol_string"] = createExportWrapper("Z3_get_symbol_string");
/** @type {function(...*):?} */
var _Z3_get_ast_kind = Module["_Z3_get_ast_kind"] = createExportWrapper("Z3_get_ast_kind");
/** @type {function(...*):?} */
var _Z3_get_ast_hash = Module["_Z3_get_ast_hash"] = createExportWrapper("Z3_get_ast_hash");
/** @type {function(...*):?} */
var _Z3_is_app = Module["_Z3_is_app"] = createExportWrapper("Z3_is_app");
/** @type {function(...*):?} */
var _Z3_to_app = Module["_Z3_to_app"] = createExportWrapper("Z3_to_app");
/** @type {function(...*):?} */
var _Z3_to_func_decl = Module["_Z3_to_func_decl"] = createExportWrapper("Z3_to_func_decl");
/** @type {function(...*):?} */
var _Z3_get_app_decl = Module["_Z3_get_app_decl"] = createExportWrapper("Z3_get_app_decl");
/** @type {function(...*):?} */
var _Z3_get_app_num_args = Module["_Z3_get_app_num_args"] = createExportWrapper("Z3_get_app_num_args");
/** @type {function(...*):?} */
var _Z3_get_app_arg = Module["_Z3_get_app_arg"] = createExportWrapper("Z3_get_app_arg");
/** @type {function(...*):?} */
var _Z3_get_decl_name = Module["_Z3_get_decl_name"] = createExportWrapper("Z3_get_decl_name");
/** @type {function(...*):?} */
var _Z3_get_decl_num_parameters = Module["_Z3_get_decl_num_parameters"] = createExportWrapper("Z3_get_decl_num_parameters");
/** @type {function(...*):?} */
var _Z3_get_decl_parameter_kind = Module["_Z3_get_decl_parameter_kind"] = createExportWrapper("Z3_get_decl_parameter_kind");
/** @type {function(...*):?} */
var _Z3_get_decl_int_parameter = Module["_Z3_get_decl_int_parameter"] = createExportWrapper("Z3_get_decl_int_parameter");
/** @type {function(...*):?} */
var _Z3_get_decl_double_parameter = Module["_Z3_get_decl_double_parameter"] = createExportWrapper("Z3_get_decl_double_parameter");
/** @type {function(...*):?} */
var _Z3_get_decl_symbol_parameter = Module["_Z3_get_decl_symbol_parameter"] = createExportWrapper("Z3_get_decl_symbol_parameter");
/** @type {function(...*):?} */
var _Z3_get_decl_sort_parameter = Module["_Z3_get_decl_sort_parameter"] = createExportWrapper("Z3_get_decl_sort_parameter");
/** @type {function(...*):?} */
var _Z3_get_decl_ast_parameter = Module["_Z3_get_decl_ast_parameter"] = createExportWrapper("Z3_get_decl_ast_parameter");
/** @type {function(...*):?} */
var _Z3_get_decl_func_decl_parameter = Module["_Z3_get_decl_func_decl_parameter"] = createExportWrapper("Z3_get_decl_func_decl_parameter");
/** @type {function(...*):?} */
var _Z3_get_decl_rational_parameter = Module["_Z3_get_decl_rational_parameter"] = createExportWrapper("Z3_get_decl_rational_parameter");
/** @type {function(...*):?} */
var _Z3_get_sort_name = Module["_Z3_get_sort_name"] = createExportWrapper("Z3_get_sort_name");
/** @type {function(...*):?} */
var _Z3_get_sort = Module["_Z3_get_sort"] = createExportWrapper("Z3_get_sort");
/** @type {function(...*):?} */
var _Z3_get_arity = Module["_Z3_get_arity"] = createExportWrapper("Z3_get_arity");
/** @type {function(...*):?} */
var _Z3_get_domain_size = Module["_Z3_get_domain_size"] = createExportWrapper("Z3_get_domain_size");
/** @type {function(...*):?} */
var _Z3_get_domain = Module["_Z3_get_domain"] = createExportWrapper("Z3_get_domain");
/** @type {function(...*):?} */
var _Z3_get_range = Module["_Z3_get_range"] = createExportWrapper("Z3_get_range");
/** @type {function(...*):?} */
var _Z3_get_bool_value = Module["_Z3_get_bool_value"] = createExportWrapper("Z3_get_bool_value");
/** @type {function(...*):?} */
var _Z3_simplify_get_help = Module["_Z3_simplify_get_help"] = createExportWrapper("Z3_simplify_get_help");
/** @type {function(...*):?} */
var _Z3_simplify_get_param_descrs = Module["_Z3_simplify_get_param_descrs"] = createExportWrapper("Z3_simplify_get_param_descrs");
/** @type {function(...*):?} */
var _Z3_update_term = Module["_Z3_update_term"] = createExportWrapper("Z3_update_term");
/** @type {function(...*):?} */
var _Z3_substitute = Module["_Z3_substitute"] = createExportWrapper("Z3_substitute");
/** @type {function(...*):?} */
var _Z3_substitute_funs = Module["_Z3_substitute_funs"] = createExportWrapper("Z3_substitute_funs");
/** @type {function(...*):?} */
var _Z3_substitute_vars = Module["_Z3_substitute_vars"] = createExportWrapper("Z3_substitute_vars");
/** @type {function(...*):?} */
var _Z3_ast_to_string = Module["_Z3_ast_to_string"] = createExportWrapper("Z3_ast_to_string");
/** @type {function(...*):?} */
var _Z3_sort_to_string = Module["_Z3_sort_to_string"] = createExportWrapper("Z3_sort_to_string");
/** @type {function(...*):?} */
var _Z3_func_decl_to_string = Module["_Z3_func_decl_to_string"] = createExportWrapper("Z3_func_decl_to_string");
/** @type {function(...*):?} */
var _Z3_benchmark_to_smtlib_string = Module["_Z3_benchmark_to_smtlib_string"] = createExportWrapper("Z3_benchmark_to_smtlib_string");
/** @type {function(...*):?} */
var _Z3_get_decl_kind = Module["_Z3_get_decl_kind"] = createExportWrapper("Z3_get_decl_kind");
/** @type {function(...*):?} */
var _Z3_get_index_value = Module["_Z3_get_index_value"] = createExportWrapper("Z3_get_index_value");
/** @type {function(...*):?} */
var _Z3_translate = Module["_Z3_translate"] = createExportWrapper("Z3_translate");
/** @type {function(...*):?} */
var _Z3_mk_params = Module["_Z3_mk_params"] = createExportWrapper("Z3_mk_params");
/** @type {function(...*):?} */
var _Z3_params_inc_ref = Module["_Z3_params_inc_ref"] = createExportWrapper("Z3_params_inc_ref");
/** @type {function(...*):?} */
var _Z3_params_dec_ref = Module["_Z3_params_dec_ref"] = createExportWrapper("Z3_params_dec_ref");
/** @type {function(...*):?} */
var _Z3_params_set_bool = Module["_Z3_params_set_bool"] = createExportWrapper("Z3_params_set_bool");
/** @type {function(...*):?} */
var _Z3_params_set_uint = Module["_Z3_params_set_uint"] = createExportWrapper("Z3_params_set_uint");
/** @type {function(...*):?} */
var _Z3_params_set_double = Module["_Z3_params_set_double"] = createExportWrapper("Z3_params_set_double");
/** @type {function(...*):?} */
var _Z3_params_set_symbol = Module["_Z3_params_set_symbol"] = createExportWrapper("Z3_params_set_symbol");
/** @type {function(...*):?} */
var _Z3_params_to_string = Module["_Z3_params_to_string"] = createExportWrapper("Z3_params_to_string");
/** @type {function(...*):?} */
var _Z3_params_validate = Module["_Z3_params_validate"] = createExportWrapper("Z3_params_validate");
/** @type {function(...*):?} */
var _Z3_param_descrs_inc_ref = Module["_Z3_param_descrs_inc_ref"] = createExportWrapper("Z3_param_descrs_inc_ref");
/** @type {function(...*):?} */
var _Z3_param_descrs_dec_ref = Module["_Z3_param_descrs_dec_ref"] = createExportWrapper("Z3_param_descrs_dec_ref");
/** @type {function(...*):?} */
var _Z3_param_descrs_get_kind = Module["_Z3_param_descrs_get_kind"] = createExportWrapper("Z3_param_descrs_get_kind");
/** @type {function(...*):?} */
var _Z3_param_descrs_size = Module["_Z3_param_descrs_size"] = createExportWrapper("Z3_param_descrs_size");
/** @type {function(...*):?} */
var _Z3_param_descrs_get_name = Module["_Z3_param_descrs_get_name"] = createExportWrapper("Z3_param_descrs_get_name");
/** @type {function(...*):?} */
var _Z3_param_descrs_get_documentation = Module["_Z3_param_descrs_get_documentation"] = createExportWrapper("Z3_param_descrs_get_documentation");
/** @type {function(...*):?} */
var _Z3_param_descrs_to_string = Module["_Z3_param_descrs_to_string"] = createExportWrapper("Z3_param_descrs_to_string");
/** @type {function(...*):?} */
var _Z3_mk_model = Module["_Z3_mk_model"] = createExportWrapper("Z3_mk_model");
/** @type {function(...*):?} */
var _Z3_model_inc_ref = Module["_Z3_model_inc_ref"] = createExportWrapper("Z3_model_inc_ref");
/** @type {function(...*):?} */
var _Z3_model_dec_ref = Module["_Z3_model_dec_ref"] = createExportWrapper("Z3_model_dec_ref");
/** @type {function(...*):?} */
var _Z3_model_get_const_interp = Module["_Z3_model_get_const_interp"] = createExportWrapper("Z3_model_get_const_interp");
/** @type {function(...*):?} */
var _Z3_model_has_interp = Module["_Z3_model_has_interp"] = createExportWrapper("Z3_model_has_interp");
/** @type {function(...*):?} */
var _Z3_model_get_func_interp = Module["_Z3_model_get_func_interp"] = createExportWrapper("Z3_model_get_func_interp");
/** @type {function(...*):?} */
var _Z3_model_get_num_consts = Module["_Z3_model_get_num_consts"] = createExportWrapper("Z3_model_get_num_consts");
/** @type {function(...*):?} */
var _Z3_model_get_const_decl = Module["_Z3_model_get_const_decl"] = createExportWrapper("Z3_model_get_const_decl");
/** @type {function(...*):?} */
var _Z3_model_get_num_funcs = Module["_Z3_model_get_num_funcs"] = createExportWrapper("Z3_model_get_num_funcs");
/** @type {function(...*):?} */
var _Z3_model_get_func_decl = Module["_Z3_model_get_func_decl"] = createExportWrapper("Z3_model_get_func_decl");
/** @type {function(...*):?} */
var _Z3_model_eval = Module["_Z3_model_eval"] = createExportWrapper("Z3_model_eval");
/** @type {function(...*):?} */
var _Z3_model_get_num_sorts = Module["_Z3_model_get_num_sorts"] = createExportWrapper("Z3_model_get_num_sorts");
/** @type {function(...*):?} */
var _Z3_model_get_sort = Module["_Z3_model_get_sort"] = createExportWrapper("Z3_model_get_sort");
/** @type {function(...*):?} */
var _Z3_model_get_sort_universe = Module["_Z3_model_get_sort_universe"] = createExportWrapper("Z3_model_get_sort_universe");
/** @type {function(...*):?} */
var _Z3_model_translate = Module["_Z3_model_translate"] = createExportWrapper("Z3_model_translate");
/** @type {function(...*):?} */
var _Z3_is_as_array = Module["_Z3_is_as_array"] = createExportWrapper("Z3_is_as_array");
/** @type {function(...*):?} */
var _Z3_get_as_array_func_decl = Module["_Z3_get_as_array_func_decl"] = createExportWrapper("Z3_get_as_array_func_decl");
/** @type {function(...*):?} */
var _Z3_add_func_interp = Module["_Z3_add_func_interp"] = createExportWrapper("Z3_add_func_interp");
/** @type {function(...*):?} */
var _Z3_add_const_interp = Module["_Z3_add_const_interp"] = createExportWrapper("Z3_add_const_interp");
/** @type {function(...*):?} */
var _Z3_func_interp_inc_ref = Module["_Z3_func_interp_inc_ref"] = createExportWrapper("Z3_func_interp_inc_ref");
/** @type {function(...*):?} */
var _Z3_func_interp_dec_ref = Module["_Z3_func_interp_dec_ref"] = createExportWrapper("Z3_func_interp_dec_ref");
/** @type {function(...*):?} */
var _Z3_func_interp_get_num_entries = Module["_Z3_func_interp_get_num_entries"] = createExportWrapper("Z3_func_interp_get_num_entries");
/** @type {function(...*):?} */
var _Z3_func_interp_get_entry = Module["_Z3_func_interp_get_entry"] = createExportWrapper("Z3_func_interp_get_entry");
/** @type {function(...*):?} */
var _Z3_func_interp_get_else = Module["_Z3_func_interp_get_else"] = createExportWrapper("Z3_func_interp_get_else");
/** @type {function(...*):?} */
var _Z3_func_interp_set_else = Module["_Z3_func_interp_set_else"] = createExportWrapper("Z3_func_interp_set_else");
/** @type {function(...*):?} */
var _Z3_func_interp_get_arity = Module["_Z3_func_interp_get_arity"] = createExportWrapper("Z3_func_interp_get_arity");
/** @type {function(...*):?} */
var _Z3_func_interp_add_entry = Module["_Z3_func_interp_add_entry"] = createExportWrapper("Z3_func_interp_add_entry");
/** @type {function(...*):?} */
var _Z3_func_entry_inc_ref = Module["_Z3_func_entry_inc_ref"] = createExportWrapper("Z3_func_entry_inc_ref");
/** @type {function(...*):?} */
var _Z3_func_entry_dec_ref = Module["_Z3_func_entry_dec_ref"] = createExportWrapper("Z3_func_entry_dec_ref");
/** @type {function(...*):?} */
var _Z3_func_entry_get_value = Module["_Z3_func_entry_get_value"] = createExportWrapper("Z3_func_entry_get_value");
/** @type {function(...*):?} */
var _Z3_func_entry_get_num_args = Module["_Z3_func_entry_get_num_args"] = createExportWrapper("Z3_func_entry_get_num_args");
/** @type {function(...*):?} */
var _Z3_func_entry_get_arg = Module["_Z3_func_entry_get_arg"] = createExportWrapper("Z3_func_entry_get_arg");
/** @type {function(...*):?} */
var _Z3_model_to_string = Module["_Z3_model_to_string"] = createExportWrapper("Z3_model_to_string");
/** @type {function(...*):?} */
var _Z3_stats_to_string = Module["_Z3_stats_to_string"] = createExportWrapper("Z3_stats_to_string");
/** @type {function(...*):?} */
var _Z3_stats_inc_ref = Module["_Z3_stats_inc_ref"] = createExportWrapper("Z3_stats_inc_ref");
/** @type {function(...*):?} */
var _Z3_stats_dec_ref = Module["_Z3_stats_dec_ref"] = createExportWrapper("Z3_stats_dec_ref");
/** @type {function(...*):?} */
var _Z3_stats_size = Module["_Z3_stats_size"] = createExportWrapper("Z3_stats_size");
/** @type {function(...*):?} */
var _Z3_stats_get_key = Module["_Z3_stats_get_key"] = createExportWrapper("Z3_stats_get_key");
/** @type {function(...*):?} */
var _Z3_stats_is_uint = Module["_Z3_stats_is_uint"] = createExportWrapper("Z3_stats_is_uint");
/** @type {function(...*):?} */
var _Z3_stats_is_double = Module["_Z3_stats_is_double"] = createExportWrapper("Z3_stats_is_double");
/** @type {function(...*):?} */
var _Z3_stats_get_uint_value = Module["_Z3_stats_get_uint_value"] = createExportWrapper("Z3_stats_get_uint_value");
/** @type {function(...*):?} */
var _Z3_stats_get_double_value = Module["_Z3_stats_get_double_value"] = createExportWrapper("Z3_stats_get_double_value");
/** @type {function(...*):?} */
var _Z3_get_estimated_alloc_size = Module["_Z3_get_estimated_alloc_size"] = createExportWrapper("Z3_get_estimated_alloc_size");
/** @type {function(...*):?} */
var _Z3_mk_ast_vector = Module["_Z3_mk_ast_vector"] = createExportWrapper("Z3_mk_ast_vector");
/** @type {function(...*):?} */
var _Z3_ast_vector_inc_ref = Module["_Z3_ast_vector_inc_ref"] = createExportWrapper("Z3_ast_vector_inc_ref");
/** @type {function(...*):?} */
var _Z3_ast_vector_dec_ref = Module["_Z3_ast_vector_dec_ref"] = createExportWrapper("Z3_ast_vector_dec_ref");
/** @type {function(...*):?} */
var _Z3_ast_vector_set = Module["_Z3_ast_vector_set"] = createExportWrapper("Z3_ast_vector_set");
/** @type {function(...*):?} */
var _Z3_ast_vector_resize = Module["_Z3_ast_vector_resize"] = createExportWrapper("Z3_ast_vector_resize");
/** @type {function(...*):?} */
var _Z3_ast_vector_push = Module["_Z3_ast_vector_push"] = createExportWrapper("Z3_ast_vector_push");
/** @type {function(...*):?} */
var _Z3_ast_vector_translate = Module["_Z3_ast_vector_translate"] = createExportWrapper("Z3_ast_vector_translate");
/** @type {function(...*):?} */
var _Z3_ast_vector_to_string = Module["_Z3_ast_vector_to_string"] = createExportWrapper("Z3_ast_vector_to_string");
/** @type {function(...*):?} */
var _Z3_mk_linear_order = Module["_Z3_mk_linear_order"] = createExportWrapper("Z3_mk_linear_order");
/** @type {function(...*):?} */
var _Z3_mk_partial_order = Module["_Z3_mk_partial_order"] = createExportWrapper("Z3_mk_partial_order");
/** @type {function(...*):?} */
var _Z3_mk_piecewise_linear_order = Module["_Z3_mk_piecewise_linear_order"] = createExportWrapper("Z3_mk_piecewise_linear_order");
/** @type {function(...*):?} */
var _Z3_mk_tree_order = Module["_Z3_mk_tree_order"] = createExportWrapper("Z3_mk_tree_order");
/** @type {function(...*):?} */
var _Z3_mk_transitive_closure = Module["_Z3_mk_transitive_closure"] = createExportWrapper("Z3_mk_transitive_closure");
/** @type {function(...*):?} */
var _Z3_mk_array_sort = Module["_Z3_mk_array_sort"] = createExportWrapper("Z3_mk_array_sort");
/** @type {function(...*):?} */
var _Z3_mk_array_sort_n = Module["_Z3_mk_array_sort_n"] = createExportWrapper("Z3_mk_array_sort_n");
/** @type {function(...*):?} */
var _Z3_mk_select = Module["_Z3_mk_select"] = createExportWrapper("Z3_mk_select");
/** @type {function(...*):?} */
var _Z3_mk_select_n = Module["_Z3_mk_select_n"] = createExportWrapper("Z3_mk_select_n");
/** @type {function(...*):?} */
var _Z3_mk_store = Module["_Z3_mk_store"] = createExportWrapper("Z3_mk_store");
/** @type {function(...*):?} */
var _Z3_mk_store_n = Module["_Z3_mk_store_n"] = createExportWrapper("Z3_mk_store_n");
/** @type {function(...*):?} */
var _Z3_mk_map = Module["_Z3_mk_map"] = createExportWrapper("Z3_mk_map");
/** @type {function(...*):?} */
var _Z3_mk_const_array = Module["_Z3_mk_const_array"] = createExportWrapper("Z3_mk_const_array");
/** @type {function(...*):?} */
var _Z3_mk_array_default = Module["_Z3_mk_array_default"] = createExportWrapper("Z3_mk_array_default");
/** @type {function(...*):?} */
var _Z3_mk_set_sort = Module["_Z3_mk_set_sort"] = createExportWrapper("Z3_mk_set_sort");
/** @type {function(...*):?} */
var _Z3_mk_empty_set = Module["_Z3_mk_empty_set"] = createExportWrapper("Z3_mk_empty_set");
/** @type {function(...*):?} */
var _Z3_mk_full_set = Module["_Z3_mk_full_set"] = createExportWrapper("Z3_mk_full_set");
/** @type {function(...*):?} */
var _Z3_mk_set_union = Module["_Z3_mk_set_union"] = createExportWrapper("Z3_mk_set_union");
/** @type {function(...*):?} */
var _Z3_mk_set_intersect = Module["_Z3_mk_set_intersect"] = createExportWrapper("Z3_mk_set_intersect");
/** @type {function(...*):?} */
var _Z3_mk_set_difference = Module["_Z3_mk_set_difference"] = createExportWrapper("Z3_mk_set_difference");
/** @type {function(...*):?} */
var _Z3_mk_set_complement = Module["_Z3_mk_set_complement"] = createExportWrapper("Z3_mk_set_complement");
/** @type {function(...*):?} */
var _Z3_mk_set_subset = Module["_Z3_mk_set_subset"] = createExportWrapper("Z3_mk_set_subset");
/** @type {function(...*):?} */
var _Z3_mk_array_ext = Module["_Z3_mk_array_ext"] = createExportWrapper("Z3_mk_array_ext");
/** @type {function(...*):?} */
var _Z3_mk_set_has_size = Module["_Z3_mk_set_has_size"] = createExportWrapper("Z3_mk_set_has_size");
/** @type {function(...*):?} */
var _Z3_mk_as_array = Module["_Z3_mk_as_array"] = createExportWrapper("Z3_mk_as_array");
/** @type {function(...*):?} */
var _Z3_mk_set_member = Module["_Z3_mk_set_member"] = createExportWrapper("Z3_mk_set_member");
/** @type {function(...*):?} */
var _Z3_mk_set_add = Module["_Z3_mk_set_add"] = createExportWrapper("Z3_mk_set_add");
/** @type {function(...*):?} */
var _Z3_mk_set_del = Module["_Z3_mk_set_del"] = createExportWrapper("Z3_mk_set_del");
/** @type {function(...*):?} */
var _Z3_get_array_sort_domain = Module["_Z3_get_array_sort_domain"] = createExportWrapper("Z3_get_array_sort_domain");
/** @type {function(...*):?} */
var _Z3_get_array_sort_domain_n = Module["_Z3_get_array_sort_domain_n"] = createExportWrapper("Z3_get_array_sort_domain_n");
/** @type {function(...*):?} */
var _Z3_get_array_sort_range = Module["_Z3_get_array_sort_range"] = createExportWrapper("Z3_get_array_sort_range");
/** @type {function(...*):?} */
var _Z3_open_log = Module["_Z3_open_log"] = createExportWrapper("Z3_open_log");
/** @type {function(...*):?} */
var _Z3_append_log = Module["_Z3_append_log"] = createExportWrapper("Z3_append_log");
/** @type {function(...*):?} */
var _Z3_close_log = Module["_Z3_close_log"] = createExportWrapper("Z3_close_log");
/** @type {function(...*):?} */
var _Z3_mk_quantifier = Module["_Z3_mk_quantifier"] = createExportWrapper("Z3_mk_quantifier");
/** @type {function(...*):?} */
var _Z3_mk_quantifier_ex = Module["_Z3_mk_quantifier_ex"] = createExportWrapper("Z3_mk_quantifier_ex");
/** @type {function(...*):?} */
var _Z3_mk_forall = Module["_Z3_mk_forall"] = createExportWrapper("Z3_mk_forall");
/** @type {function(...*):?} */
var _Z3_mk_exists = Module["_Z3_mk_exists"] = createExportWrapper("Z3_mk_exists");
/** @type {function(...*):?} */
var _Z3_mk_lambda = Module["_Z3_mk_lambda"] = createExportWrapper("Z3_mk_lambda");
/** @type {function(...*):?} */
var _Z3_mk_lambda_const = Module["_Z3_mk_lambda_const"] = createExportWrapper("Z3_mk_lambda_const");
/** @type {function(...*):?} */
var _Z3_mk_quantifier_const_ex = Module["_Z3_mk_quantifier_const_ex"] = createExportWrapper("Z3_mk_quantifier_const_ex");
/** @type {function(...*):?} */
var _Z3_mk_quantifier_const = Module["_Z3_mk_quantifier_const"] = createExportWrapper("Z3_mk_quantifier_const");
/** @type {function(...*):?} */
var _Z3_mk_forall_const = Module["_Z3_mk_forall_const"] = createExportWrapper("Z3_mk_forall_const");
/** @type {function(...*):?} */
var _Z3_mk_exists_const = Module["_Z3_mk_exists_const"] = createExportWrapper("Z3_mk_exists_const");
/** @type {function(...*):?} */
var _Z3_mk_pattern = Module["_Z3_mk_pattern"] = createExportWrapper("Z3_mk_pattern");
/** @type {function(...*):?} */
var _Z3_mk_bound = Module["_Z3_mk_bound"] = createExportWrapper("Z3_mk_bound");
/** @type {function(...*):?} */
var _Z3_is_quantifier_forall = Module["_Z3_is_quantifier_forall"] = createExportWrapper("Z3_is_quantifier_forall");
/** @type {function(...*):?} */
var _Z3_is_quantifier_exists = Module["_Z3_is_quantifier_exists"] = createExportWrapper("Z3_is_quantifier_exists");
/** @type {function(...*):?} */
var _Z3_is_lambda = Module["_Z3_is_lambda"] = createExportWrapper("Z3_is_lambda");
/** @type {function(...*):?} */
var _Z3_get_quantifier_weight = Module["_Z3_get_quantifier_weight"] = createExportWrapper("Z3_get_quantifier_weight");
/** @type {function(...*):?} */
var _Z3_get_quantifier_num_patterns = Module["_Z3_get_quantifier_num_patterns"] = createExportWrapper("Z3_get_quantifier_num_patterns");
/** @type {function(...*):?} */
var _Z3_get_quantifier_pattern_ast = Module["_Z3_get_quantifier_pattern_ast"] = createExportWrapper("Z3_get_quantifier_pattern_ast");
/** @type {function(...*):?} */
var _Z3_get_quantifier_num_no_patterns = Module["_Z3_get_quantifier_num_no_patterns"] = createExportWrapper("Z3_get_quantifier_num_no_patterns");
/** @type {function(...*):?} */
var _Z3_get_quantifier_no_pattern_ast = Module["_Z3_get_quantifier_no_pattern_ast"] = createExportWrapper("Z3_get_quantifier_no_pattern_ast");
/** @type {function(...*):?} */
var _Z3_get_quantifier_bound_name = Module["_Z3_get_quantifier_bound_name"] = createExportWrapper("Z3_get_quantifier_bound_name");
/** @type {function(...*):?} */
var _Z3_get_quantifier_bound_sort = Module["_Z3_get_quantifier_bound_sort"] = createExportWrapper("Z3_get_quantifier_bound_sort");
/** @type {function(...*):?} */
var _Z3_get_quantifier_body = Module["_Z3_get_quantifier_body"] = createExportWrapper("Z3_get_quantifier_body");
/** @type {function(...*):?} */
var _Z3_get_quantifier_num_bound = Module["_Z3_get_quantifier_num_bound"] = createExportWrapper("Z3_get_quantifier_num_bound");
/** @type {function(...*):?} */
var _Z3_get_pattern_num_terms = Module["_Z3_get_pattern_num_terms"] = createExportWrapper("Z3_get_pattern_num_terms");
/** @type {function(...*):?} */
var _Z3_get_pattern = Module["_Z3_get_pattern"] = createExportWrapper("Z3_get_pattern");
/** @type {function(...*):?} */
var _Z3_pattern_to_ast = Module["_Z3_pattern_to_ast"] = createExportWrapper("Z3_pattern_to_ast");
/** @type {function(...*):?} */
var _Z3_pattern_to_string = Module["_Z3_pattern_to_string"] = createExportWrapper("Z3_pattern_to_string");
/** @type {function(...*):?} */
var _Z3_mk_optimize = Module["_Z3_mk_optimize"] = createExportWrapper("Z3_mk_optimize");
/** @type {function(...*):?} */
var _Z3_optimize_inc_ref = Module["_Z3_optimize_inc_ref"] = createExportWrapper("Z3_optimize_inc_ref");
/** @type {function(...*):?} */
var _Z3_optimize_dec_ref = Module["_Z3_optimize_dec_ref"] = createExportWrapper("Z3_optimize_dec_ref");
/** @type {function(...*):?} */
var _Z3_optimize_assert = Module["_Z3_optimize_assert"] = createExportWrapper("Z3_optimize_assert");
/** @type {function(...*):?} */
var _Z3_optimize_assert_and_track = Module["_Z3_optimize_assert_and_track"] = createExportWrapper("Z3_optimize_assert_and_track");
/** @type {function(...*):?} */
var _Z3_optimize_assert_soft = Module["_Z3_optimize_assert_soft"] = createExportWrapper("Z3_optimize_assert_soft");
/** @type {function(...*):?} */
var _Z3_optimize_maximize = Module["_Z3_optimize_maximize"] = createExportWrapper("Z3_optimize_maximize");
/** @type {function(...*):?} */
var _Z3_optimize_minimize = Module["_Z3_optimize_minimize"] = createExportWrapper("Z3_optimize_minimize");
/** @type {function(...*):?} */
var _Z3_optimize_push = Module["_Z3_optimize_push"] = createExportWrapper("Z3_optimize_push");
/** @type {function(...*):?} */
var _Z3_optimize_pop = Module["_Z3_optimize_pop"] = createExportWrapper("Z3_optimize_pop");
/** @type {function(...*):?} */
var _Z3_optimize_get_unsat_core = Module["_Z3_optimize_get_unsat_core"] = createExportWrapper("Z3_optimize_get_unsat_core");
/** @type {function(...*):?} */
var _Z3_optimize_get_reason_unknown = Module["_Z3_optimize_get_reason_unknown"] = createExportWrapper("Z3_optimize_get_reason_unknown");
/** @type {function(...*):?} */
var _Z3_optimize_get_model = Module["_Z3_optimize_get_model"] = createExportWrapper("Z3_optimize_get_model");
/** @type {function(...*):?} */
var _Z3_optimize_set_params = Module["_Z3_optimize_set_params"] = createExportWrapper("Z3_optimize_set_params");
/** @type {function(...*):?} */
var _Z3_optimize_get_param_descrs = Module["_Z3_optimize_get_param_descrs"] = createExportWrapper("Z3_optimize_get_param_descrs");
/** @type {function(...*):?} */
var _Z3_optimize_get_lower = Module["_Z3_optimize_get_lower"] = createExportWrapper("Z3_optimize_get_lower");
/** @type {function(...*):?} */
var _Z3_optimize_get_upper = Module["_Z3_optimize_get_upper"] = createExportWrapper("Z3_optimize_get_upper");
/** @type {function(...*):?} */
var _Z3_optimize_get_lower_as_vector = Module["_Z3_optimize_get_lower_as_vector"] = createExportWrapper("Z3_optimize_get_lower_as_vector");
/** @type {function(...*):?} */
var _Z3_optimize_get_upper_as_vector = Module["_Z3_optimize_get_upper_as_vector"] = createExportWrapper("Z3_optimize_get_upper_as_vector");
/** @type {function(...*):?} */
var _Z3_optimize_to_string = Module["_Z3_optimize_to_string"] = createExportWrapper("Z3_optimize_to_string");
/** @type {function(...*):?} */
var _Z3_optimize_get_help = Module["_Z3_optimize_get_help"] = createExportWrapper("Z3_optimize_get_help");
/** @type {function(...*):?} */
var _Z3_optimize_get_statistics = Module["_Z3_optimize_get_statistics"] = createExportWrapper("Z3_optimize_get_statistics");
/** @type {function(...*):?} */
var _Z3_optimize_from_string = Module["_Z3_optimize_from_string"] = createExportWrapper("Z3_optimize_from_string");
/** @type {function(...*):?} */
var _Z3_optimize_from_file = Module["_Z3_optimize_from_file"] = createExportWrapper("Z3_optimize_from_file");
/** @type {function(...*):?} */
var _Z3_optimize_get_assertions = Module["_Z3_optimize_get_assertions"] = createExportWrapper("Z3_optimize_get_assertions");
/** @type {function(...*):?} */
var _Z3_optimize_get_objectives = Module["_Z3_optimize_get_objectives"] = createExportWrapper("Z3_optimize_get_objectives");
/** @type {function(...*):?} */
var _Z3_mk_bv_sort = Module["_Z3_mk_bv_sort"] = createExportWrapper("Z3_mk_bv_sort");
/** @type {function(...*):?} */
var _Z3_mk_bvnot = Module["_Z3_mk_bvnot"] = createExportWrapper("Z3_mk_bvnot");
/** @type {function(...*):?} */
var _Z3_mk_bvredand = Module["_Z3_mk_bvredand"] = createExportWrapper("Z3_mk_bvredand");
/** @type {function(...*):?} */
var _Z3_mk_bvredor = Module["_Z3_mk_bvredor"] = createExportWrapper("Z3_mk_bvredor");
/** @type {function(...*):?} */
var _Z3_mk_bvand = Module["_Z3_mk_bvand"] = createExportWrapper("Z3_mk_bvand");
/** @type {function(...*):?} */
var _Z3_mk_bvor = Module["_Z3_mk_bvor"] = createExportWrapper("Z3_mk_bvor");
/** @type {function(...*):?} */
var _Z3_mk_bvxor = Module["_Z3_mk_bvxor"] = createExportWrapper("Z3_mk_bvxor");
/** @type {function(...*):?} */
var _Z3_mk_bvnand = Module["_Z3_mk_bvnand"] = createExportWrapper("Z3_mk_bvnand");
/** @type {function(...*):?} */
var _Z3_mk_bvnor = Module["_Z3_mk_bvnor"] = createExportWrapper("Z3_mk_bvnor");
/** @type {function(...*):?} */
var _Z3_mk_bvxnor = Module["_Z3_mk_bvxnor"] = createExportWrapper("Z3_mk_bvxnor");
/** @type {function(...*):?} */
var _Z3_mk_bvadd = Module["_Z3_mk_bvadd"] = createExportWrapper("Z3_mk_bvadd");
/** @type {function(...*):?} */
var _Z3_mk_bvmul = Module["_Z3_mk_bvmul"] = createExportWrapper("Z3_mk_bvmul");
/** @type {function(...*):?} */
var _Z3_mk_bvudiv = Module["_Z3_mk_bvudiv"] = createExportWrapper("Z3_mk_bvudiv");
/** @type {function(...*):?} */
var _Z3_mk_bvsdiv = Module["_Z3_mk_bvsdiv"] = createExportWrapper("Z3_mk_bvsdiv");
/** @type {function(...*):?} */
var _Z3_mk_bvurem = Module["_Z3_mk_bvurem"] = createExportWrapper("Z3_mk_bvurem");
/** @type {function(...*):?} */
var _Z3_mk_bvsrem = Module["_Z3_mk_bvsrem"] = createExportWrapper("Z3_mk_bvsrem");
/** @type {function(...*):?} */
var _Z3_mk_bvsmod = Module["_Z3_mk_bvsmod"] = createExportWrapper("Z3_mk_bvsmod");
/** @type {function(...*):?} */
var _Z3_mk_bvule = Module["_Z3_mk_bvule"] = createExportWrapper("Z3_mk_bvule");
/** @type {function(...*):?} */
var _Z3_mk_bvsle = Module["_Z3_mk_bvsle"] = createExportWrapper("Z3_mk_bvsle");
/** @type {function(...*):?} */
var _Z3_mk_bvuge = Module["_Z3_mk_bvuge"] = createExportWrapper("Z3_mk_bvuge");
/** @type {function(...*):?} */
var _Z3_mk_bvsge = Module["_Z3_mk_bvsge"] = createExportWrapper("Z3_mk_bvsge");
/** @type {function(...*):?} */
var _Z3_mk_bvult = Module["_Z3_mk_bvult"] = createExportWrapper("Z3_mk_bvult");
/** @type {function(...*):?} */
var _Z3_mk_bvslt = Module["_Z3_mk_bvslt"] = createExportWrapper("Z3_mk_bvslt");
/** @type {function(...*):?} */
var _Z3_mk_bvugt = Module["_Z3_mk_bvugt"] = createExportWrapper("Z3_mk_bvugt");
/** @type {function(...*):?} */
var _Z3_mk_bvsgt = Module["_Z3_mk_bvsgt"] = createExportWrapper("Z3_mk_bvsgt");
/** @type {function(...*):?} */
var _Z3_mk_concat = Module["_Z3_mk_concat"] = createExportWrapper("Z3_mk_concat");
/** @type {function(...*):?} */
var _Z3_mk_bvshl = Module["_Z3_mk_bvshl"] = createExportWrapper("Z3_mk_bvshl");
/** @type {function(...*):?} */
var _Z3_mk_bvlshr = Module["_Z3_mk_bvlshr"] = createExportWrapper("Z3_mk_bvlshr");
/** @type {function(...*):?} */
var _Z3_mk_bvashr = Module["_Z3_mk_bvashr"] = createExportWrapper("Z3_mk_bvashr");
/** @type {function(...*):?} */
var _Z3_mk_ext_rotate_left = Module["_Z3_mk_ext_rotate_left"] = createExportWrapper("Z3_mk_ext_rotate_left");
/** @type {function(...*):?} */
var _Z3_mk_ext_rotate_right = Module["_Z3_mk_ext_rotate_right"] = createExportWrapper("Z3_mk_ext_rotate_right");
/** @type {function(...*):?} */
var _Z3_mk_extract = Module["_Z3_mk_extract"] = createExportWrapper("Z3_mk_extract");
/** @type {function(...*):?} */
var _Z3_mk_sign_ext = Module["_Z3_mk_sign_ext"] = createExportWrapper("Z3_mk_sign_ext");
/** @type {function(...*):?} */
var _Z3_mk_zero_ext = Module["_Z3_mk_zero_ext"] = createExportWrapper("Z3_mk_zero_ext");
/** @type {function(...*):?} */
var _Z3_mk_repeat = Module["_Z3_mk_repeat"] = createExportWrapper("Z3_mk_repeat");
/** @type {function(...*):?} */
var _Z3_mk_bit2bool = Module["_Z3_mk_bit2bool"] = createExportWrapper("Z3_mk_bit2bool");
/** @type {function(...*):?} */
var _Z3_mk_rotate_left = Module["_Z3_mk_rotate_left"] = createExportWrapper("Z3_mk_rotate_left");
/** @type {function(...*):?} */
var _Z3_mk_rotate_right = Module["_Z3_mk_rotate_right"] = createExportWrapper("Z3_mk_rotate_right");
/** @type {function(...*):?} */
var _Z3_mk_int2bv = Module["_Z3_mk_int2bv"] = createExportWrapper("Z3_mk_int2bv");
/** @type {function(...*):?} */
var _Z3_mk_bv2int = Module["_Z3_mk_bv2int"] = createExportWrapper("Z3_mk_bv2int");
/** @type {function(...*):?} */
var _Z3_get_bv_sort_size = Module["_Z3_get_bv_sort_size"] = createExportWrapper("Z3_get_bv_sort_size");
/** @type {function(...*):?} */
var _Z3_mk_bvadd_no_overflow = Module["_Z3_mk_bvadd_no_overflow"] = createExportWrapper("Z3_mk_bvadd_no_overflow");
/** @type {function(...*):?} */
var _Z3_mk_bvadd_no_underflow = Module["_Z3_mk_bvadd_no_underflow"] = createExportWrapper("Z3_mk_bvadd_no_underflow");
/** @type {function(...*):?} */
var _Z3_mk_bvsub_no_overflow = Module["_Z3_mk_bvsub_no_overflow"] = createExportWrapper("Z3_mk_bvsub_no_overflow");
/** @type {function(...*):?} */
var _Z3_mk_bvneg = Module["_Z3_mk_bvneg"] = createExportWrapper("Z3_mk_bvneg");
/** @type {function(...*):?} */
var _Z3_mk_bvsub_no_underflow = Module["_Z3_mk_bvsub_no_underflow"] = createExportWrapper("Z3_mk_bvsub_no_underflow");
/** @type {function(...*):?} */
var _Z3_mk_bvmul_no_overflow = Module["_Z3_mk_bvmul_no_overflow"] = createExportWrapper("Z3_mk_bvmul_no_overflow");
/** @type {function(...*):?} */
var _Z3_mk_bvmul_no_underflow = Module["_Z3_mk_bvmul_no_underflow"] = createExportWrapper("Z3_mk_bvmul_no_underflow");
/** @type {function(...*):?} */
var _Z3_mk_bvneg_no_overflow = Module["_Z3_mk_bvneg_no_overflow"] = createExportWrapper("Z3_mk_bvneg_no_overflow");
/** @type {function(...*):?} */
var _Z3_mk_bvsdiv_no_overflow = Module["_Z3_mk_bvsdiv_no_overflow"] = createExportWrapper("Z3_mk_bvsdiv_no_overflow");
/** @type {function(...*):?} */
var _Z3_mk_bvsub = Module["_Z3_mk_bvsub"] = createExportWrapper("Z3_mk_bvsub");
/** @type {function(...*):?} */
var _Z3_qe_model_project = Module["_Z3_qe_model_project"] = createExportWrapper("Z3_qe_model_project");
/** @type {function(...*):?} */
var _Z3_qe_model_project_skolem = Module["_Z3_qe_model_project_skolem"] = createExportWrapper("Z3_qe_model_project_skolem");
/** @type {function(...*):?} */
var _Z3_model_extrapolate = Module["_Z3_model_extrapolate"] = createExportWrapper("Z3_model_extrapolate");
/** @type {function(...*):?} */
var _Z3_qe_lite = Module["_Z3_qe_lite"] = createExportWrapper("Z3_qe_lite");
/** @type {function(...*):?} */
var _Z3_mk_int_sort = Module["_Z3_mk_int_sort"] = createExportWrapper("Z3_mk_int_sort");
/** @type {function(...*):?} */
var _Z3_mk_real_sort = Module["_Z3_mk_real_sort"] = createExportWrapper("Z3_mk_real_sort");
/** @type {function(...*):?} */
var _Z3_mk_real_int64 = Module["_Z3_mk_real_int64"] = createExportWrapper("Z3_mk_real_int64");
/** @type {function(...*):?} */
var _Z3_mk_real = Module["_Z3_mk_real"] = createExportWrapper("Z3_mk_real");
/** @type {function(...*):?} */
var _Z3_mk_add = Module["_Z3_mk_add"] = createExportWrapper("Z3_mk_add");
/** @type {function(...*):?} */
var _Z3_mk_mul = Module["_Z3_mk_mul"] = createExportWrapper("Z3_mk_mul");
/** @type {function(...*):?} */
var _Z3_mk_power = Module["_Z3_mk_power"] = createExportWrapper("Z3_mk_power");
/** @type {function(...*):?} */
var _Z3_mk_mod = Module["_Z3_mk_mod"] = createExportWrapper("Z3_mk_mod");
/** @type {function(...*):?} */
var _Z3_mk_rem = Module["_Z3_mk_rem"] = createExportWrapper("Z3_mk_rem");
/** @type {function(...*):?} */
var _Z3_mk_div = Module["_Z3_mk_div"] = createExportWrapper("Z3_mk_div");
/** @type {function(...*):?} */
var _Z3_mk_lt = Module["_Z3_mk_lt"] = createExportWrapper("Z3_mk_lt");
/** @type {function(...*):?} */
var _Z3_mk_gt = Module["_Z3_mk_gt"] = createExportWrapper("Z3_mk_gt");
/** @type {function(...*):?} */
var _Z3_mk_le = Module["_Z3_mk_le"] = createExportWrapper("Z3_mk_le");
/** @type {function(...*):?} */
var _Z3_mk_ge = Module["_Z3_mk_ge"] = createExportWrapper("Z3_mk_ge");
/** @type {function(...*):?} */
var _Z3_mk_divides = Module["_Z3_mk_divides"] = createExportWrapper("Z3_mk_divides");
/** @type {function(...*):?} */
var _Z3_mk_int2real = Module["_Z3_mk_int2real"] = createExportWrapper("Z3_mk_int2real");
/** @type {function(...*):?} */
var _Z3_mk_real2int = Module["_Z3_mk_real2int"] = createExportWrapper("Z3_mk_real2int");
/** @type {function(...*):?} */
var _Z3_mk_is_int = Module["_Z3_mk_is_int"] = createExportWrapper("Z3_mk_is_int");
/** @type {function(...*):?} */
var _Z3_mk_sub = Module["_Z3_mk_sub"] = createExportWrapper("Z3_mk_sub");
/** @type {function(...*):?} */
var _Z3_mk_unary_minus = Module["_Z3_mk_unary_minus"] = createExportWrapper("Z3_mk_unary_minus");
/** @type {function(...*):?} */
var _Z3_is_algebraic_number = Module["_Z3_is_algebraic_number"] = createExportWrapper("Z3_is_algebraic_number");
/** @type {function(...*):?} */
var _Z3_get_algebraic_number_lower = Module["_Z3_get_algebraic_number_lower"] = createExportWrapper("Z3_get_algebraic_number_lower");
/** @type {function(...*):?} */
var _Z3_get_algebraic_number_upper = Module["_Z3_get_algebraic_number_upper"] = createExportWrapper("Z3_get_algebraic_number_upper");
/** @type {function(...*):?} */
var _Z3_get_numerator = Module["_Z3_get_numerator"] = createExportWrapper("Z3_get_numerator");
/** @type {function(...*):?} */
var _Z3_get_denominator = Module["_Z3_get_denominator"] = createExportWrapper("Z3_get_denominator");
/** @type {function(...*):?} */
var _Z3_mk_goal = Module["_Z3_mk_goal"] = createExportWrapper("Z3_mk_goal");
/** @type {function(...*):?} */
var _Z3_goal_inc_ref = Module["_Z3_goal_inc_ref"] = createExportWrapper("Z3_goal_inc_ref");
/** @type {function(...*):?} */
var _Z3_goal_dec_ref = Module["_Z3_goal_dec_ref"] = createExportWrapper("Z3_goal_dec_ref");
/** @type {function(...*):?} */
var _Z3_goal_precision = Module["_Z3_goal_precision"] = createExportWrapper("Z3_goal_precision");
/** @type {function(...*):?} */
var _Z3_goal_assert = Module["_Z3_goal_assert"] = createExportWrapper("Z3_goal_assert");
/** @type {function(...*):?} */
var _Z3_goal_inconsistent = Module["_Z3_goal_inconsistent"] = createExportWrapper("Z3_goal_inconsistent");
/** @type {function(...*):?} */
var _Z3_goal_depth = Module["_Z3_goal_depth"] = createExportWrapper("Z3_goal_depth");
/** @type {function(...*):?} */
var _Z3_goal_reset = Module["_Z3_goal_reset"] = createExportWrapper("Z3_goal_reset");
/** @type {function(...*):?} */
var _Z3_goal_size = Module["_Z3_goal_size"] = createExportWrapper("Z3_goal_size");
/** @type {function(...*):?} */
var _Z3_goal_formula = Module["_Z3_goal_formula"] = createExportWrapper("Z3_goal_formula");
/** @type {function(...*):?} */
var _Z3_goal_num_exprs = Module["_Z3_goal_num_exprs"] = createExportWrapper("Z3_goal_num_exprs");
/** @type {function(...*):?} */
var _Z3_goal_is_decided_sat = Module["_Z3_goal_is_decided_sat"] = createExportWrapper("Z3_goal_is_decided_sat");
/** @type {function(...*):?} */
var _Z3_goal_is_decided_unsat = Module["_Z3_goal_is_decided_unsat"] = createExportWrapper("Z3_goal_is_decided_unsat");
/** @type {function(...*):?} */
var _Z3_goal_convert_model = Module["_Z3_goal_convert_model"] = createExportWrapper("Z3_goal_convert_model");
/** @type {function(...*):?} */
var _Z3_goal_translate = Module["_Z3_goal_translate"] = createExportWrapper("Z3_goal_translate");
/** @type {function(...*):?} */
var _Z3_goal_to_string = Module["_Z3_goal_to_string"] = createExportWrapper("Z3_goal_to_string");
/** @type {function(...*):?} */
var _Z3_goal_to_dimacs_string = Module["_Z3_goal_to_dimacs_string"] = createExportWrapper("Z3_goal_to_dimacs_string");
/** @type {function(...*):?} */
var _Z3_mk_parser_context = Module["_Z3_mk_parser_context"] = createExportWrapper("Z3_mk_parser_context");
/** @type {function(...*):?} */
var _Z3_parser_context_inc_ref = Module["_Z3_parser_context_inc_ref"] = createExportWrapper("Z3_parser_context_inc_ref");
/** @type {function(...*):?} */
var _Z3_parser_context_dec_ref = Module["_Z3_parser_context_dec_ref"] = createExportWrapper("Z3_parser_context_dec_ref");
/** @type {function(...*):?} */
var _Z3_parser_context_add_sort = Module["_Z3_parser_context_add_sort"] = createExportWrapper("Z3_parser_context_add_sort");
/** @type {function(...*):?} */
var _Z3_parser_context_add_decl = Module["_Z3_parser_context_add_decl"] = createExportWrapper("Z3_parser_context_add_decl");
/** @type {function(...*):?} */
var _Z3_parser_context_from_string = Module["_Z3_parser_context_from_string"] = createExportWrapper("Z3_parser_context_from_string");
/** @type {function(...*):?} */
var _Z3_parse_smtlib2_string = Module["_Z3_parse_smtlib2_string"] = createExportWrapper("Z3_parse_smtlib2_string");
/** @type {function(...*):?} */
var _Z3_parse_smtlib2_file = Module["_Z3_parse_smtlib2_file"] = createExportWrapper("Z3_parse_smtlib2_file");
/** @type {function(...*):?} */
var _Z3_mk_fpa_rounding_mode_sort = Module["_Z3_mk_fpa_rounding_mode_sort"] = createExportWrapper("Z3_mk_fpa_rounding_mode_sort");
/** @type {function(...*):?} */
var _Z3_mk_fpa_round_nearest_ties_to_even = Module["_Z3_mk_fpa_round_nearest_ties_to_even"] = createExportWrapper("Z3_mk_fpa_round_nearest_ties_to_even");
/** @type {function(...*):?} */
var _Z3_mk_fpa_rne = Module["_Z3_mk_fpa_rne"] = createExportWrapper("Z3_mk_fpa_rne");
/** @type {function(...*):?} */
var _Z3_mk_fpa_round_nearest_ties_to_away = Module["_Z3_mk_fpa_round_nearest_ties_to_away"] = createExportWrapper("Z3_mk_fpa_round_nearest_ties_to_away");
/** @type {function(...*):?} */
var _Z3_mk_fpa_rna = Module["_Z3_mk_fpa_rna"] = createExportWrapper("Z3_mk_fpa_rna");
/** @type {function(...*):?} */
var _Z3_mk_fpa_round_toward_positive = Module["_Z3_mk_fpa_round_toward_positive"] = createExportWrapper("Z3_mk_fpa_round_toward_positive");
/** @type {function(...*):?} */
var _Z3_mk_fpa_rtp = Module["_Z3_mk_fpa_rtp"] = createExportWrapper("Z3_mk_fpa_rtp");
/** @type {function(...*):?} */
var _Z3_mk_fpa_round_toward_negative = Module["_Z3_mk_fpa_round_toward_negative"] = createExportWrapper("Z3_mk_fpa_round_toward_negative");
/** @type {function(...*):?} */
var _Z3_mk_fpa_rtn = Module["_Z3_mk_fpa_rtn"] = createExportWrapper("Z3_mk_fpa_rtn");
/** @type {function(...*):?} */
var _Z3_mk_fpa_round_toward_zero = Module["_Z3_mk_fpa_round_toward_zero"] = createExportWrapper("Z3_mk_fpa_round_toward_zero");
/** @type {function(...*):?} */
var _Z3_mk_fpa_rtz = Module["_Z3_mk_fpa_rtz"] = createExportWrapper("Z3_mk_fpa_rtz");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort = Module["_Z3_mk_fpa_sort"] = createExportWrapper("Z3_mk_fpa_sort");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_half = Module["_Z3_mk_fpa_sort_half"] = createExportWrapper("Z3_mk_fpa_sort_half");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_16 = Module["_Z3_mk_fpa_sort_16"] = createExportWrapper("Z3_mk_fpa_sort_16");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_single = Module["_Z3_mk_fpa_sort_single"] = createExportWrapper("Z3_mk_fpa_sort_single");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_32 = Module["_Z3_mk_fpa_sort_32"] = createExportWrapper("Z3_mk_fpa_sort_32");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_double = Module["_Z3_mk_fpa_sort_double"] = createExportWrapper("Z3_mk_fpa_sort_double");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_64 = Module["_Z3_mk_fpa_sort_64"] = createExportWrapper("Z3_mk_fpa_sort_64");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_quadruple = Module["_Z3_mk_fpa_sort_quadruple"] = createExportWrapper("Z3_mk_fpa_sort_quadruple");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sort_128 = Module["_Z3_mk_fpa_sort_128"] = createExportWrapper("Z3_mk_fpa_sort_128");
/** @type {function(...*):?} */
var _Z3_mk_fpa_nan = Module["_Z3_mk_fpa_nan"] = createExportWrapper("Z3_mk_fpa_nan");
/** @type {function(...*):?} */
var _Z3_mk_fpa_inf = Module["_Z3_mk_fpa_inf"] = createExportWrapper("Z3_mk_fpa_inf");
/** @type {function(...*):?} */
var _Z3_mk_fpa_zero = Module["_Z3_mk_fpa_zero"] = createExportWrapper("Z3_mk_fpa_zero");
/** @type {function(...*):?} */
var _Z3_mk_fpa_fp = Module["_Z3_mk_fpa_fp"] = createExportWrapper("Z3_mk_fpa_fp");
/** @type {function(...*):?} */
var _Z3_mk_fpa_numeral_float = Module["_Z3_mk_fpa_numeral_float"] = createExportWrapper("Z3_mk_fpa_numeral_float");
/** @type {function(...*):?} */
var _Z3_mk_fpa_numeral_double = Module["_Z3_mk_fpa_numeral_double"] = createExportWrapper("Z3_mk_fpa_numeral_double");
/** @type {function(...*):?} */
var _Z3_mk_fpa_numeral_int = Module["_Z3_mk_fpa_numeral_int"] = createExportWrapper("Z3_mk_fpa_numeral_int");
/** @type {function(...*):?} */
var _Z3_mk_fpa_numeral_int_uint = Module["_Z3_mk_fpa_numeral_int_uint"] = createExportWrapper("Z3_mk_fpa_numeral_int_uint");
/** @type {function(...*):?} */
var _Z3_mk_fpa_numeral_int64_uint64 = Module["_Z3_mk_fpa_numeral_int64_uint64"] = createExportWrapper("Z3_mk_fpa_numeral_int64_uint64");
/** @type {function(...*):?} */
var _Z3_mk_fpa_abs = Module["_Z3_mk_fpa_abs"] = createExportWrapper("Z3_mk_fpa_abs");
/** @type {function(...*):?} */
var _Z3_mk_fpa_neg = Module["_Z3_mk_fpa_neg"] = createExportWrapper("Z3_mk_fpa_neg");
/** @type {function(...*):?} */
var _Z3_mk_fpa_add = Module["_Z3_mk_fpa_add"] = createExportWrapper("Z3_mk_fpa_add");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sub = Module["_Z3_mk_fpa_sub"] = createExportWrapper("Z3_mk_fpa_sub");
/** @type {function(...*):?} */
var _Z3_mk_fpa_mul = Module["_Z3_mk_fpa_mul"] = createExportWrapper("Z3_mk_fpa_mul");
/** @type {function(...*):?} */
var _Z3_mk_fpa_div = Module["_Z3_mk_fpa_div"] = createExportWrapper("Z3_mk_fpa_div");
/** @type {function(...*):?} */
var _Z3_mk_fpa_fma = Module["_Z3_mk_fpa_fma"] = createExportWrapper("Z3_mk_fpa_fma");
/** @type {function(...*):?} */
var _Z3_mk_fpa_sqrt = Module["_Z3_mk_fpa_sqrt"] = createExportWrapper("Z3_mk_fpa_sqrt");
/** @type {function(...*):?} */
var _Z3_mk_fpa_rem = Module["_Z3_mk_fpa_rem"] = createExportWrapper("Z3_mk_fpa_rem");
/** @type {function(...*):?} */
var _Z3_mk_fpa_round_to_integral = Module["_Z3_mk_fpa_round_to_integral"] = createExportWrapper("Z3_mk_fpa_round_to_integral");
/** @type {function(...*):?} */
var _Z3_mk_fpa_min = Module["_Z3_mk_fpa_min"] = createExportWrapper("Z3_mk_fpa_min");
/** @type {function(...*):?} */
var _Z3_mk_fpa_max = Module["_Z3_mk_fpa_max"] = createExportWrapper("Z3_mk_fpa_max");
/** @type {function(...*):?} */
var _Z3_mk_fpa_leq = Module["_Z3_mk_fpa_leq"] = createExportWrapper("Z3_mk_fpa_leq");
/** @type {function(...*):?} */
var _Z3_mk_fpa_lt = Module["_Z3_mk_fpa_lt"] = createExportWrapper("Z3_mk_fpa_lt");
/** @type {function(...*):?} */
var _Z3_mk_fpa_geq = Module["_Z3_mk_fpa_geq"] = createExportWrapper("Z3_mk_fpa_geq");
/** @type {function(...*):?} */
var _Z3_mk_fpa_gt = Module["_Z3_mk_fpa_gt"] = createExportWrapper("Z3_mk_fpa_gt");
/** @type {function(...*):?} */
var _Z3_mk_fpa_eq = Module["_Z3_mk_fpa_eq"] = createExportWrapper("Z3_mk_fpa_eq");
/** @type {function(...*):?} */
var _Z3_mk_fpa_is_normal = Module["_Z3_mk_fpa_is_normal"] = createExportWrapper("Z3_mk_fpa_is_normal");
/** @type {function(...*):?} */
var _Z3_mk_fpa_is_subnormal = Module["_Z3_mk_fpa_is_subnormal"] = createExportWrapper("Z3_mk_fpa_is_subnormal");
/** @type {function(...*):?} */
var _Z3_mk_fpa_is_zero = Module["_Z3_mk_fpa_is_zero"] = createExportWrapper("Z3_mk_fpa_is_zero");
/** @type {function(...*):?} */
var _Z3_mk_fpa_is_infinite = Module["_Z3_mk_fpa_is_infinite"] = createExportWrapper("Z3_mk_fpa_is_infinite");
/** @type {function(...*):?} */
var _Z3_mk_fpa_is_nan = Module["_Z3_mk_fpa_is_nan"] = createExportWrapper("Z3_mk_fpa_is_nan");
/** @type {function(...*):?} */
var _Z3_mk_fpa_is_negative = Module["_Z3_mk_fpa_is_negative"] = createExportWrapper("Z3_mk_fpa_is_negative");
/** @type {function(...*):?} */
var _Z3_mk_fpa_is_positive = Module["_Z3_mk_fpa_is_positive"] = createExportWrapper("Z3_mk_fpa_is_positive");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_fp_bv = Module["_Z3_mk_fpa_to_fp_bv"] = createExportWrapper("Z3_mk_fpa_to_fp_bv");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_fp_float = Module["_Z3_mk_fpa_to_fp_float"] = createExportWrapper("Z3_mk_fpa_to_fp_float");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_fp_real = Module["_Z3_mk_fpa_to_fp_real"] = createExportWrapper("Z3_mk_fpa_to_fp_real");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_fp_signed = Module["_Z3_mk_fpa_to_fp_signed"] = createExportWrapper("Z3_mk_fpa_to_fp_signed");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_fp_unsigned = Module["_Z3_mk_fpa_to_fp_unsigned"] = createExportWrapper("Z3_mk_fpa_to_fp_unsigned");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_ubv = Module["_Z3_mk_fpa_to_ubv"] = createExportWrapper("Z3_mk_fpa_to_ubv");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_sbv = Module["_Z3_mk_fpa_to_sbv"] = createExportWrapper("Z3_mk_fpa_to_sbv");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_real = Module["_Z3_mk_fpa_to_real"] = createExportWrapper("Z3_mk_fpa_to_real");
/** @type {function(...*):?} */
var _Z3_fpa_get_ebits = Module["_Z3_fpa_get_ebits"] = createExportWrapper("Z3_fpa_get_ebits");
/** @type {function(...*):?} */
var _Z3_fpa_get_sbits = Module["_Z3_fpa_get_sbits"] = createExportWrapper("Z3_fpa_get_sbits");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_sign = Module["_Z3_fpa_get_numeral_sign"] = createExportWrapper("Z3_fpa_get_numeral_sign");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_sign_bv = Module["_Z3_fpa_get_numeral_sign_bv"] = createExportWrapper("Z3_fpa_get_numeral_sign_bv");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_significand_bv = Module["_Z3_fpa_get_numeral_significand_bv"] = createExportWrapper("Z3_fpa_get_numeral_significand_bv");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_significand_string = Module["_Z3_fpa_get_numeral_significand_string"] = createExportWrapper("Z3_fpa_get_numeral_significand_string");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_significand_uint64 = Module["_Z3_fpa_get_numeral_significand_uint64"] = createExportWrapper("Z3_fpa_get_numeral_significand_uint64");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_exponent_string = Module["_Z3_fpa_get_numeral_exponent_string"] = createExportWrapper("Z3_fpa_get_numeral_exponent_string");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_exponent_int64 = Module["_Z3_fpa_get_numeral_exponent_int64"] = createExportWrapper("Z3_fpa_get_numeral_exponent_int64");
/** @type {function(...*):?} */
var _Z3_fpa_get_numeral_exponent_bv = Module["_Z3_fpa_get_numeral_exponent_bv"] = createExportWrapper("Z3_fpa_get_numeral_exponent_bv");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_ieee_bv = Module["_Z3_mk_fpa_to_ieee_bv"] = createExportWrapper("Z3_mk_fpa_to_ieee_bv");
/** @type {function(...*):?} */
var _Z3_mk_fpa_to_fp_int_real = Module["_Z3_mk_fpa_to_fp_int_real"] = createExportWrapper("Z3_mk_fpa_to_fp_int_real");
/** @type {function(...*):?} */
var _Z3_fpa_is_numeral_nan = Module["_Z3_fpa_is_numeral_nan"] = createExportWrapper("Z3_fpa_is_numeral_nan");
/** @type {function(...*):?} */
var _Z3_fpa_is_numeral_inf = Module["_Z3_fpa_is_numeral_inf"] = createExportWrapper("Z3_fpa_is_numeral_inf");
/** @type {function(...*):?} */
var _Z3_fpa_is_numeral_zero = Module["_Z3_fpa_is_numeral_zero"] = createExportWrapper("Z3_fpa_is_numeral_zero");
/** @type {function(...*):?} */
var _Z3_fpa_is_numeral_normal = Module["_Z3_fpa_is_numeral_normal"] = createExportWrapper("Z3_fpa_is_numeral_normal");
/** @type {function(...*):?} */
var _Z3_fpa_is_numeral_subnormal = Module["_Z3_fpa_is_numeral_subnormal"] = createExportWrapper("Z3_fpa_is_numeral_subnormal");
/** @type {function(...*):?} */
var _Z3_fpa_is_numeral_positive = Module["_Z3_fpa_is_numeral_positive"] = createExportWrapper("Z3_fpa_is_numeral_positive");
/** @type {function(...*):?} */
var _Z3_fpa_is_numeral_negative = Module["_Z3_fpa_is_numeral_negative"] = createExportWrapper("Z3_fpa_is_numeral_negative");
/** @type {function(...*):?} */
var _fflush = Module["_fflush"] = createExportWrapper("fflush");
/** @type {function(...*):?} */
var _free = Module["_free"] = createExportWrapper("free");
/** @type {function(...*):?} */
var _malloc = createExportWrapper("malloc");
/** @type {function(...*):?} */
var __emscripten_tls_init = Module["__emscripten_tls_init"] = createExportWrapper("_emscripten_tls_init");
/** @type {function(...*):?} */
var ___errno_location = createExportWrapper("__errno_location");
/** @type {function(...*):?} */
var __emscripten_thread_init = Module["__emscripten_thread_init"] = createExportWrapper("_emscripten_thread_init");
/** @type {function(...*):?} */
var __emscripten_thread_crashed = Module["__emscripten_thread_crashed"] = createExportWrapper("_emscripten_thread_crashed");
/** @type {function(...*):?} */
var _emscripten_main_thread_process_queued_calls = createExportWrapper("emscripten_main_thread_process_queued_calls");
/** @type {function(...*):?} */
var _emscripten_main_browser_thread_id = createExportWrapper("emscripten_main_browser_thread_id");
/** @type {function(...*):?} */
var __emscripten_run_in_main_runtime_thread_js = createExportWrapper("_emscripten_run_in_main_runtime_thread_js");
/** @type {function(...*):?} */
var _emscripten_dispatch_to_thread_ = createExportWrapper("emscripten_dispatch_to_thread_");
/** @type {function(...*):?} */
var _emscripten_stack_get_base = function() {
  return (_emscripten_stack_get_base = Module["asm"]["emscripten_stack_get_base"]).apply(null, arguments);
};

/** @type {function(...*):?} */
var _emscripten_stack_get_end = function() {
  return (_emscripten_stack_get_end = Module["asm"]["emscripten_stack_get_end"]).apply(null, arguments);
};

/** @type {function(...*):?} */
var __emscripten_proxy_execute_task_queue = Module["__emscripten_proxy_execute_task_queue"] = createExportWrapper("_emscripten_proxy_execute_task_queue");
/** @type {function(...*):?} */
var __emscripten_thread_free_data = createExportWrapper("_emscripten_thread_free_data");
/** @type {function(...*):?} */
var __emscripten_thread_exit = Module["__emscripten_thread_exit"] = createExportWrapper("_emscripten_thread_exit");
/** @type {function(...*):?} */
var _setThrew = createExportWrapper("setThrew");
/** @type {function(...*):?} */
var setTempRet0 = createExportWrapper("setTempRet0");
/** @type {function(...*):?} */
var _emscripten_stack_init = function() {
  return (_emscripten_stack_init = Module["asm"]["emscripten_stack_init"]).apply(null, arguments);
};

/** @type {function(...*):?} */
var _emscripten_stack_set_limits = function() {
  return (_emscripten_stack_set_limits = Module["asm"]["emscripten_stack_set_limits"]).apply(null, arguments);
};

/** @type {function(...*):?} */
var _emscripten_stack_get_free = function() {
  return (_emscripten_stack_get_free = Module["asm"]["emscripten_stack_get_free"]).apply(null, arguments);
};

/** @type {function(...*):?} */
var stackSave = createExportWrapper("stackSave");
/** @type {function(...*):?} */
var stackRestore = createExportWrapper("stackRestore");
/** @type {function(...*):?} */
var stackAlloc = createExportWrapper("stackAlloc");
/** @type {function(...*):?} */
var _emscripten_stack_get_current = function() {
  return (_emscripten_stack_get_current = Module["asm"]["emscripten_stack_get_current"]).apply(null, arguments);
};

/** @type {function(...*):?} */
var ___cxa_demangle = createExportWrapper("__cxa_demangle");
/** @type {function(...*):?} */
var ___get_exception_message = Module["___get_exception_message"] = createExportWrapper("__get_exception_message");
/** @type {function(...*):?} */
var ___cxa_can_catch = createExportWrapper("__cxa_can_catch");
/** @type {function(...*):?} */
var ___cxa_is_pointer_type = createExportWrapper("__cxa_is_pointer_type");

function invoke_iii(index,a1,a2) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viii(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vi(index,a1) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_ii(index,a1) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiii(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vii(index,a1,a2) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_i(index) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)();
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiii(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiii(index,a1,a2,a3,a4,a5) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_v(index) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)();
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiii(index,a1,a2,a3,a4,a5) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiiiii(index,a1,a2,a3,a4,a5,a6,a7) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiii(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiii(index,a1,a2,a3,a4,a5,a6) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiiii(index,a1,a2,a3,a4,a5,a6) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viid(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiii(index,a1,a2,a3,a4,a5,a6,a7) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vid(index,a1,a2) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_id(index,a1) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_dii(index,a1,a2) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_j(index) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)();
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
    return 0n;
  }
}

function invoke_iid(index,a1,a2) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiid(index,a1,a2,a3,a4,a5) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viij(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiij(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viji(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_jii(index,a1,a2) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
    return 0n;
  }
}

function invoke_iiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiid(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiji(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_jiij(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
    return 0n;
  }
}

function invoke_viiiiiji(index,a1,a2,a3,a4,a5,a6,a7) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iij(index,a1,a2) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_ji(index,a1) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
    return 0n;
  }
}

function invoke_diiid(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_diid(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_di(index,a1) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_diii(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_jiii(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
    return 0n;
  }
}

function invoke_viiiiij(index,a1,a2,a3,a4,a5,a6) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_fiiii(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viidi(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiid(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vidii(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiji(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vij(index,a1,a2) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_fii(index,a1,a2) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iijii(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiij(index,a1,a2,a3,a4,a5) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_iiiiid(index,a1,a2,a3,a4,a5) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_jiiii(index,a1,a2,a3,a4) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
    return 0n;
  }
}

function invoke_iiiiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_fiii(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    return getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiiiiiiiiiiii(index,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vifi(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiif(index,a1,a2,a3,a4,a5) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vidi(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viijji(index,a1,a2,a3,a4,a5) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_viiiiijj(index,a1,a2,a3,a4,a5,a6,a7) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3,a4,a5,a6,a7);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}

function invoke_vijj(index,a1,a2,a3) {
  var sp = stackSave();
  try {
    getWasmTableEntry(index)(a1,a2,a3);
  } catch(e) {
    stackRestore(sp);
    if (!(e instanceof EmscriptenEH)) throw e;
    _setThrew(1, 0);
  }
}


// include: postamble.js
// === Auto-generated postamble setup entry stuff ===

Module["UTF8ToString"] = UTF8ToString;
Module["keepRuntimeAlive"] = keepRuntimeAlive;
Module["wasmMemory"] = wasmMemory;
Module["ccall"] = ccall;
Module["intArrayFromString"] = intArrayFromString;
Module["ExitStatus"] = ExitStatus;
Module["FS"] = FS;
Module["ALLOC_NORMAL"] = ALLOC_NORMAL;
Module["allocate"] = allocate;
Module["PThread"] = PThread;
var missingLibrarySymbols = [
  'stringToNewUTF8',
  'emscripten_realloc_buffer',
  'inetPton4',
  'inetNtop4',
  'inetPton6',
  'inetNtop6',
  'readSockaddr',
  'writeSockaddr',
  'getHostByName',
  'traverseStack',
  'convertPCtoSourceLocation',
  'runEmAsmFunction',
  'jstoi_q',
  'jstoi_s',
  'listenOnce',
  'autoResumeAudioContext',
  'getDynCaller',
  'dynCall',
  'runtimeKeepalivePush',
  'runtimeKeepalivePop',
  'callUserCallback',
  'maybeExit',
  'safeSetTimeout',
  'asmjsMangle',
  'HandleAllocator',
  'getNativeTypeSize',
  'STACK_SIZE',
  'STACK_ALIGN',
  'POINTER_SIZE',
  'ASSERTIONS',
  'writeI53ToI64',
  'writeI53ToI64Clamped',
  'writeI53ToI64Signaling',
  'writeI53ToU64Clamped',
  'writeI53ToU64Signaling',
  'readI53FromI64',
  'readI53FromU64',
  'convertI32PairToI53',
  'convertI32PairToI53Checked',
  'convertU32PairToI53',
  'cwrap',
  'uleb128Encode',
  'sigToWasmTypes',
  'generateFuncType',
  'convertJsFunctionToWasm',
  'getEmptyTableSlot',
  'updateTableMap',
  'getFunctionAddress',
  'addFunction',
  'removeFunction',
  'reallyNegative',
  'unSign',
  'strLen',
  'reSign',
  'formatString',
  'intArrayToString',
  'AsciiToString',
  'stringToAscii',
  'UTF16ToString',
  'stringToUTF16',
  'lengthBytesUTF16',
  'UTF32ToString',
  'stringToUTF32',
  'lengthBytesUTF32',
  'allocateUTF8',
  'allocateUTF8OnStack',
  'writeStringToMemory',
  'getSocketFromFD',
  'getSocketAddress',
  'registerKeyEventCallback',
  'maybeCStringToJsString',
  'findEventTarget',
  'findCanvasEventTarget',
  'getBoundingClientRect',
  'fillMouseEventData',
  'registerMouseEventCallback',
  'registerWheelEventCallback',
  'registerUiEventCallback',
  'registerFocusEventCallback',
  'fillDeviceOrientationEventData',
  'registerDeviceOrientationEventCallback',
  'fillDeviceMotionEventData',
  'registerDeviceMotionEventCallback',
  'screenOrientation',
  'fillOrientationChangeEventData',
  'registerOrientationChangeEventCallback',
  'fillFullscreenChangeEventData',
  'registerFullscreenChangeEventCallback',
  'JSEvents_requestFullscreen',
  'JSEvents_resizeCanvasForFullscreen',
  'registerRestoreOldStyle',
  'hideEverythingExceptGivenElement',
  'restoreHiddenElements',
  'setLetterbox',
  'softFullscreenResizeWebGLRenderTarget',
  'doRequestFullscreen',
  'fillPointerlockChangeEventData',
  'registerPointerlockChangeEventCallback',
  'registerPointerlockErrorEventCallback',
  'requestPointerLock',
  'fillVisibilityChangeEventData',
  'registerVisibilityChangeEventCallback',
  'registerTouchEventCallback',
  'fillGamepadEventData',
  'registerGamepadEventCallback',
  'registerBeforeUnloadEventCallback',
  'fillBatteryEventData',
  'battery',
  'registerBatteryEventCallback',
  'setCanvasElementSize',
  'getCanvasElementSize',
  'checkWasiClock',
  'createDyncallWrapper',
  'setImmediateWrapped',
  'clearImmediateWrapped',
  'polyfillSetImmediate',
  'getPromise',
  'makePromise',
  'makePromiseCallback',
  'setMainLoop',
  '_setNetworkCallback',
  'heapObjectForWebGLType',
  'heapAccessShiftForWebGLHeap',
  'emscriptenWebGLGet',
  'computeUnpackAlignedImageSize',
  'emscriptenWebGLGetTexPixelData',
  'emscriptenWebGLGetUniform',
  'webglGetUniformLocation',
  'webglPrepareUniformLocationsBeforeFirstUse',
  'webglGetLeftBracePos',
  'emscriptenWebGLGetVertexAttrib',
  'writeGLArray',
  'SDL_unicode',
  'SDL_ttfContext',
  'SDL_audio',
  'GLFW_Window',
  'runAndAbortIfError',
];
missingLibrarySymbols.forEach(missingLibrarySymbol)

var unexportedSymbols = [
  'run',
  'UTF8ArrayToString',
  'stringToUTF8Array',
  'stringToUTF8',
  'lengthBytesUTF8',
  'addOnPreRun',
  'addOnInit',
  'addOnPreMain',
  'addOnExit',
  'addOnPostRun',
  'addRunDependency',
  'removeRunDependency',
  'FS_createFolder',
  'FS_createPath',
  'FS_createDataFile',
  'FS_createPreloadedFile',
  'FS_createLazyFile',
  'FS_createLink',
  'FS_createDevice',
  'FS_unlink',
  'out',
  'err',
  'callMain',
  'abort',
  'stackAlloc',
  'stackSave',
  'stackRestore',
  'getTempRet0',
  'setTempRet0',
  'writeStackCookie',
  'checkStackCookie',
  'ptrToString',
  'zeroMemory',
  'exitJS',
  'getHeapMax',
  'abortOnCannotGrowMemory',
  'ENV',
  'ERRNO_CODES',
  'ERRNO_MESSAGES',
  'setErrNo',
  'DNS',
  'Protocols',
  'Sockets',
  'getRandomDevice',
  'timers',
  'warnOnce',
  'UNWIND_CACHE',
  'readEmAsmArgsArray',
  'readEmAsmArgs',
  'runMainThreadEmAsm',
  'getExecutableName',
  'handleException',
  'asyncLoad',
  'alignMemory',
  'mmapAlloc',
  'MAX_INT53',
  'MIN_INT53',
  'bigintToI53Checked',
  'getCFunc',
  'freeTableIndexes',
  'functionsInTableMap',
  'setValue',
  'getValue',
  'PATH',
  'PATH_FS',
  'UTF16Decoder',
  'writeArrayToMemory',
  'writeAsciiToMemory',
  'SYSCALLS',
  'JSEvents',
  'specialHTMLTargets',
  'currentFullscreenStrategy',
  'restoreOldWindowedStyle',
  'demangle',
  'demangleAll',
  'jsStackTrace',
  'stackTrace',
  'getEnvStrings',
  'doReadv',
  'doWritev',
  'dlopenMissingError',
  'promiseMap',
  'uncaughtExceptionCount',
  'exceptionLast',
  'exceptionCaught',
  'ExceptionInfo',
  'exception_addRef',
  'exception_decRef',
  'getExceptionMessageCommon',
  'incrementExceptionRefcount',
  'decrementExceptionRefcount',
  'getExceptionMessage',
  'Browser',
  'wget',
  'MEMFS',
  'TTY',
  'PIPEFS',
  'SOCKFS',
  'tempFixedLengthArray',
  'miniTempWebGLFloatBuffers',
  'GL',
  'AL',
  'SDL',
  'SDL_gfx',
  'GLUT',
  'EGL',
  'GLFW',
  'GLEW',
  'IDBStore',
  'ALLOC_STACK',
  'terminateWorker',
  'killThread',
  'cleanupThread',
  'registerTLSInit',
  'cancelThread',
  'spawnThread',
  'exitOnMainThread',
  'invokeEntryPoint',
  'executeNotifiedProxyingQueue',
];
unexportedSymbols.forEach(unexportedRuntimeSymbol);



var calledRun;

dependenciesFulfilled = function runCaller() {
  // If run has never been called, and we should call run (INVOKE_RUN is true, and Module.noInitialRun is not false)
  if (!calledRun) run();
  if (!calledRun) dependenciesFulfilled = runCaller; // try this again later, after new deps are fulfilled
};

function stackCheckInit() {
  // This is normally called automatically during __wasm_call_ctors but need to
  // get these values before even running any of the ctors so we call it redundantly
  // here.
  // See $establishStackSpace for the equivelent code that runs on a thread
  assert(!ENVIRONMENT_IS_PTHREAD);
  _emscripten_stack_init();
  // TODO(sbc): Move writeStackCookie to native to to avoid this.
  writeStackCookie();
}

function run() {

  if (runDependencies > 0) {
    return;
  }

  if (!ENVIRONMENT_IS_PTHREAD)
    stackCheckInit();

  if (ENVIRONMENT_IS_PTHREAD) {
    // The promise resolve function typically gets called as part of the execution
    // of `doRun` below. The workers/pthreads don't execute `doRun` so the
    // creation promise can be resolved, marking the pthread-Module as initialized.
    readyPromiseResolve(Module);
    initRuntime();
    startWorker(Module);
    return;
  }

  preRun();

  // a preRun added a dependency, run will be called later
  if (runDependencies > 0) {
    return;
  }

  function doRun() {
    // run may have just been called through dependencies being fulfilled just in this very frame,
    // or while the async setStatus time below was happening
    if (calledRun) return;
    calledRun = true;
    Module['calledRun'] = true;

    if (ABORT) return;

    initRuntime();

    readyPromiseResolve(Module);
    if (Module['onRuntimeInitialized']) Module['onRuntimeInitialized']();

    assert(!Module['_main'], 'compiled without a main, but one is present. if you added it from JS, use Module["onRuntimeInitialized"]');

    postRun();
  }

  if (Module['setStatus']) {
    Module['setStatus']('Running...');
    setTimeout(function() {
      setTimeout(function() {
        Module['setStatus']('');
      }, 1);
      doRun();
    }, 1);
  } else
  {
    doRun();
  }
  checkStackCookie();
}

function checkUnflushedContent() {
  // Compiler settings do not allow exiting the runtime, so flushing
  // the streams is not possible. but in ASSERTIONS mode we check
  // if there was something to flush, and if so tell the user they
  // should request that the runtime be exitable.
  // Normally we would not even include flush() at all, but in ASSERTIONS
  // builds we do so just for this check, and here we see if there is any
  // content to flush, that is, we check if there would have been
  // something a non-ASSERTIONS build would have not seen.
  // How we flush the streams depends on whether we are in SYSCALLS_REQUIRE_FILESYSTEM=0
  // mode (which has its own special function for this; otherwise, all
  // the code is inside libc)
  var oldOut = out;
  var oldErr = err;
  var has = false;
  out = err = (x) => {
    has = true;
  }
  try { // it doesn't matter if it fails
    _fflush(0);
    // also flush in the JS FS layer
    ['stdout', 'stderr'].forEach(function(name) {
      var info = FS.analyzePath('/dev/' + name);
      if (!info) return;
      var stream = info.object;
      var rdev = stream.rdev;
      var tty = TTY.ttys[rdev];
      if (tty && tty.output && tty.output.length) {
        has = true;
      }
    });
  } catch(e) {}
  out = oldOut;
  err = oldErr;
  if (has) {
    warnOnce('stdio streams had content in them that was not flushed. you should set EXIT_RUNTIME to 1 (see the FAQ), or make sure to emit a newline when you printf etc.');
  }
}

if (Module['preInit']) {
  if (typeof Module['preInit'] == 'function') Module['preInit'] = [Module['preInit']];
  while (Module['preInit'].length > 0) {
    Module['preInit'].pop()();
  }
}

run();


// end include: postamble.js


  return initZ3.ready
}

);
})();
if (typeof exports === 'object' && typeof module === 'object')
  module.exports = initZ3;
else if (typeof define === 'function' && define['amd'])
  define([], function() { return initZ3; });
else if (typeof exports === 'object')
  exports["initZ3"] = initZ3;
