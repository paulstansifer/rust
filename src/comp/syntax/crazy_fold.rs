


/* In the absence of macro keywords, we'll use an ad-hoc system to denote the 
   different kinds of other values we want to examine:
     - []: node_id
     - [[]]: span
     - [leaf_name]: leaf
     - node_name: ordinary node
     - [seq, node_name]: vector of nodes
     - [opt, node_name]: option of node
     - [seq, [seq, node_name]]: vector of options of node
  Makes perfect sense, eh?

 */

/* the `n_`-prefixed names are not needed for any of this; we can get rid 
of them if we don't need to implement a serializer before a snapshot cycle. */

tag tree[T] { leaf(T); seq(@[tree[T]], span); }

// match result
type mr[T] = option::t[tree[T]];

fn option_flatten_map[T, U](f: &fn(&T) -> option::t[U] , v: &[T]) ->
   option::t[[U]] {
    let res = ~[];
    for elem: T  in v {
        alt f(elem) { none. { ret none; } some(fv) { res += ~[fv]; } }
    }
    ret some(res);
}


fn tree_map[T](t: tree[T], f: fn(T) -> mr[U]) -> mr[U] {
    alt t {
      leaf(x) { f(x) }
      seq(trees, span) {
        alt option_flatten_map(bind tree_map(_, f), *trees) {
          none. { none }
          some(real_trees) { some(seq(@real_trees, span)) }
        }
      }
    }
}

fn compose_mr_fns[T,U,V](f1: fn(T) -> mr[U], f2: fn(U) -> mr[V]) 
    -> fn(T) -> mr[V] {
    lambda(t) {
        alt f1(t) {
          none. { none }
          some(matches) { trees(matches, f2) }
        }
    }
}

type gen_selector[T] = fn(&T) -> gen_node;
type binders[T] = {real_binders: hashmap[ident, gen_selector[T]],
                   mutable literal_ast_matchers: [gen_selector[T]]};

fn dummy() {
    #macro[[#desp[ex], ex.node]];
    #macro[[#resp[ex], {node: ex, span: x.span} ]]; //unhygienic

    #macro[[#noop[ex], ex]];

    #macro[[#r[do_box, respan, despan, tagname, n_tagname, [elts, ...]],
            // having separately-named functions would be great, but would
            // require macros-in-ID-positions
            tagname = {
                pattern_to_selectors:
                // in the future, whyen this is organized less insanely,
                // it'd be nice to have a parameter rather than just `expr`.
                fn(cx: &ext_ctxt, x_: @tagname, s: &fn(&expr) -> @tagname, 
                   b: &binders) {
                    let x = #despan[x_];
                    #r_pts_core[elts, ...];
                }
                transcribe: 
                fn(cx &ext_ctxt, x_: @tagname, b: &bindings) -> @tagname {
                    ret #respan[
                        
                    ]
                }
                find_free_vars:
                fn(cx: &ext_ctxt, x_: @tagname) -> [ident] {
                    let x = #despan[x_];
                    #r_ffv_core
                }
            }
           ]];

    #macro[[#r_pts_core[[]], {}],
           [#r_pts_core[[field_name, n_field_name, extractor], elts, ...],
            //cx and x and s and b are being used unhygienically here
            //they will need to be passed as arguments when we have hygiene
            {
                let new_s = compose_mr_fns(s, {|other_x| other_x.field_name});
                tagname.pattern_to_selectors(cx, x.field_name, new_s, b);
                #r_pts_core[elts, ...];
            }
           ]];
    #macro[[#r_ffv_core[[]], {}],
           [#r_ffv_core[[field_name, n_field_name, extractor]],
            {
                tagname.find_free_vars()
            }
           ]]

    #macro[[#pts_elt[v, [[]]], /*span*/ {} ],
           [#pts_elt[v, []], /*node_id*/ {} ],
           [#pts_elt[v, [leaf_name]], /*we may need to handle ident*/ {}],
           [#pts_elt[v, [seq, extractor]],
            for vi in v {
                #pts_elt[vi, extractor];
            }],
           [#pts_elt[v, [opt, extractor]],
            alt v {
              none. {}
              some(vi) {#pts_elt[vi, extractor]; }
            }],
           [#pts_elt[v, node_type],
            node_type.pattern_to_selectors(v);]];
    
    /* ugliness needed until `...` in arbitrary positions is supported. */
    #macro[[#r_trans_core[[f0, nf0, ex0], [f1, nf2, ex1]],
            {f0: #trans_elt[x.f0, ex0],
             f1: #trans_elt[x.f1, ex1]}],
           [#r_trans_core[[f0, nf0, ex0], [f1, nf2, ex1], [f2, nf2, ex2]],
            {f0: #trans_elt[x.f0, ex0],
             f1: #trans_elt[x.f1, ex1],
             f2: #trans_elt[x.f2, ex2]}],
           [#r_trans_core[[f0, nf0, ex0], [f1, nf2, ex1], [f2, nf2, ex2], 
                          [f3, nf3, ex3]],
            {f0: #trans_elt[x.f0, ex0],
             f1: #trans_elt[x.f1, ex1],
             f2: #trans_elt[x.f2, ex2],
             f0: #trans_elt[x.f3, ex3]}]
           [#r_trans_core[[f0, nf0, ex0], [f1, nf2, ex1], [f2, nf2, ex2], 
                          [f3, nf3, ex3], [f4, nf4, ex4]]
            {f0: #trans_elt[x.f0, ex0],
             f1: #trans_elt[x.f1, ex1],
             f2: #trans_elt[x.f2, ex2],
             f0: #trans_elt[x.f3, ex3],
             f1: #trans_elt[x.f4, ex4]}]
           [#r_trans_core[[f0, nf0, ex0], [f1, nf2, ex1], [f2, nf2, ex2], 
                          [f3, nf3, ex3], [f4, nf4, ex4], [f5, nf5, ex5]]
            {f0: #trans_elt[x.f0, ex0],
             f1: #trans_elt[x.f1, ex1],
             f2: #trans_elt[x.f2, ex2],
             f3: #trans_elt[x.f3, ex3],
             f4: #trans_elt[x.f4, ex4],
             f5: #trans_elt[x.f5, ex5]}]];
    
    #macro[[#trans_elt[v, [[]]], /*span*/ x_.span ], /*unhygienic*/
           [#trans_elt[v, []], /*node_id*/ cx.next_id() ],
           [#trans_elt[v, [leaf_name]], v],
           [#trans_elt[v, [seq, extractor]],
            for vi in v {
                #trans_elt[vi, extractor];
            }],
           [#trans_elt[v, [opt, extractor]],
            alt v {
              none. {}
              some(vi) {#trans_elt[vi, extractor]; }
            }]];

        

    // arguments explicitly structured here (instead of writing `args, ...`)
    // to make error messages easier to deal with.
    #macro[[#br_alt[val, ctx, [[tagname, n_tagname, [elt, ...]],
                              more_tags, ...]],
            #br_alt_gen[do_span, val, ctx, [[tagname, n_tagname, [elt, ...]],
                                           more_tags, ...]]]];
    #macro[[#br_alt_no_span[val, ctx,
                            [[tagname, n_tagname, [elt, ...]],
                             more_tags, ...]],
            #br_alt_gen[do_not_span, val, ctx,
                        [[tagname, n_tagname, [elt, ...]], more_tags, ...]]]];

    // the silly `n_tagname` will be replacable with an invocation of
    // #concat_idents after subtitution into arbitrary AST nodes works
    #macro[[#br_alt_gen[possibly_span, val, ctx,
                        [[tagname, n_tagname, [elt, ...]], more_tags, ...]],
            alt val {
              branch(n_tagname., sp, chldrn) {
                #possibly_span[sp, #br_alt_core[ctx, sp, tagname,
                                                chldrn, 0u, [elt, ...], []]]
              }
              //replace this explicit recursion with `...`, once it works
              //over all kinds of AST nodes.
              _ { #br_alt_gen[possibly_span, val, ctx, [more_tags, ...]] }
            }],
           [#br_alt_gen[possibly_span, val, ctx, []],
            alt val {
              branch(_, sp, _) {
                ctx.ff(sp, "expected " + #ident_to_str[tagname])
              }
              _ { ctx.ff(none, "expected " + #ident_to_str[tagname]) }
            }]];

    // this wackiness is just because we need indices
    #macro[[#br_alt_core[ctx, sp, ctor, kids, offset, [], []],
            ctor], //special case, for the syntax special case for empty tags
           [#br_alt_core[ctx, sp, ctor, kids, offset, [h, more_hs, ...],
                         [accum, ...]],
            #br_alt_core[ctx, sp, ctor, kids, offset+1u, [more_hs, ...],
                         [accum, ...,
                          #extract_elt[ctx, sp, kids, offset, h]]]],
           [#br_alt_core[ctx, sp, ctor, kids, offset, [], [accum, ...]],
            ctor(accum, ...)]];



    #macro[[#br_rec[args, ...], #br_rec_gen[do_span, args, ...]]];
    #macro[[#br_rec_no_span[args, ...], #br_rec_gen[do_not_span, args, ...]]];


    #macro[[#br_rec_gen[possibly_span, val, ctx, tagname, n_tagname, fields],
            alt val {
              branch(n_tagname., sp, chldrn) {
                #possibly_span[sp, #br_rec_core[ctx, sp, chldrn, fields]]
              }
              branch(_, sp, _) {
                ctx.ff(sp, "expected " + #ident_to_str[tagname])
              }
              _ { ctx.ff(option::none, "expected " + #ident_to_str[tagname]) }
            }]];



    //this abomination can go away when `...` works properly over
    //all kinds of AST nodes.
    #macro[[#br_rec_core[ctx, sp, kids, [[f0, fh0]]],
            {f0: #extract_elt[ctx, sp, kids, 0u, fh0]}],
           [#br_rec_core[ctx, sp, kids, [[f0, fh0], [f1, fh1]]],
            {f0: #extract_elt[ctx, sp, kids, 0u, fh0],
             f1: #extract_elt[ctx, sp, kids, 1u, fh1]}],
           [#br_rec_core[ctx, sp, kids, [[f0, fh0], [f1, fh1], [f2, fh2]]],
            {f0: #extract_elt[ctx, sp, kids, 0u, fh0],
             f1: #extract_elt[ctx, sp, kids, 1u, fh1],
             f2: #extract_elt[ctx, sp, kids, 2u, fh2]}],
           [#br_rec_core[ctx, sp, kids,
                         [[f0, fh0], [f1, fh1], [f2, fh2], [f3, fh3]]],
            {f0: #extract_elt[ctx, sp, kids, 0u, fh0],
             f1: #extract_elt[ctx, sp, kids, 1u, fh1],
             f2: #extract_elt[ctx, sp, kids, 2u, fh2],
             f3: #extract_elt[ctx, sp, kids, 3u, fh3]}],
           [#br_rec_core[ctx, sp, kids,
                         [[f0, fh0], [f1, fh1], [f2, fh2], [f3, fh3],
                          [f4, fh4]]],
            {f0: #extract_elt[ctx, sp, kids, 0u, fh0],
             f1: #extract_elt[ctx, sp, kids, 1u, fh1],
             f2: #extract_elt[ctx, sp, kids, 2u, fh2],
             f3: #extract_elt[ctx, sp, kids, 3u, fh3],
             f4: #extract_elt[ctx, sp, kids, 4u, fh4]}],
           [#br_rec_core[ctx, sp, kids,
                         [[f0, fh0], [f1, fh1], [f2, fh2], [f3, fh3],
                          [f4, fh4], [f5, fh5]]],
            {f0: #extract_elt[ctx, sp, kids, 0u, fh0],
             f1: #extract_elt[ctx, sp, kids, 1u, fh1],
             f2: #extract_elt[ctx, sp, kids, 2u, fh2],
             f3: #extract_elt[ctx, sp, kids, 3u, fh3],
             f4: #extract_elt[ctx, sp, kids, 4u, fh4],
             f5: #extract_elt[ctx, sp, kids, 5u, fh5]}]];

    #macro[[#opt[extractor], ???]
    #macro[[#seq[extractor], ???]


    #macro[ //keywords would make these two nicer:
        [#extract_elt[ctx, sp, elts, idx, []], ctx.next_id()],
        [#extract_elt[ctx, sp, elts, idx, [[]]], 
         alt sp {
               some(s) { s }
               none. { ctx.ff(none, "needed a span"); }
             }],
        [#extract_elt[ctx, sp, elts, idx, [handler, extractor]],
         #handler[#extract_elt[ctx, sp, elts, idx, extractor]]];
        [#extract_elt[ctx, sp, elts, idx, [leaf_destructure]],
         alt *elts.(idx) {
           leaf_destructure(x) { x }
           _ {
             ctx.ff(sp, #fmt["expected %s in position %u",
                             #ident_to_str[leaf_destructure], idx])
           }
         }],
        [#extract_elt[ctx, sp, elts, idx, extract_fn],
         #concat_idents[cv,extract_fn](ctx, elts.(idx))]];
}


#r[do_box, ensp, desp, crate, n_crate,
   [[directives, [seq, crate_directive]],
    [module, _mod],
    [attrs, [seq, attribute]],
    [config, [seq, meta_item]]]];

#a[do_box, ensp, desp, crate_directive,
   [[cdir_src_mod, n_cdir_src_mod,
     [[l_ident], [l_optional_filename], [seq, attribute]]],
    [cdir_dir_mod, n_cdir_dir_mod,
     [[l_ident], [l_optional_filename], [seq, crate_directive], 
      [seq, attribute]]],
    [cdir_view_item, n_cdir_view_item, [view_item]],
    [cdir_syntax, n_cdir_syntax,       [[l_path]]],
    [cdir_auth, n_cdir_auth,           [[l_path], [l__auth]]]]];

#a[do_box, ensp, desp, meta_item,
   [[meta_word, n_meta_word,             [[l_ident]]],
    [meta_list, n_meta_list,             [[l_ident], [seq, meta_item]]],
    [meta_name_value, n_meta_name_value, [[l_ident], lit]]]];

#r[no_box, ensp, desp, blk, n_blk,
   [[stmts, [seq, stmt]],
    [expr,  [opt, expr]],
    [id,    [l_node_id]]]];

#r[do_box, noop, noop, pat, n_pat,
   [[id, []],
    [node, pat_],
    [span, [[]]]]];

#a[no_box, noop, noop, pat_,
   //FIXME: _tup and _lit are missing
   [[pat_wild, n_pat_wild, []],
    [pat_bind, n_pat_bind, [[l_ident]]],
    [pat_tag, n_pat_tag,   [[l_path], [seq, pat]]],
    [pat_rec, n_pat_rec,   [[seq, field_pat], [l_bool]]],
    [pat_box, n_pat_box,   [pat]]]];

#r[no_box, noop, noop, field_pat, n_field_pat,
   [[ident, [l_ident]], [pat, pat]]];

#a[do_box, ensp, desp, stmt,
   [[stmt_decl, n_stmt_decl, [decl, []]],
    [stmt_expr, n_stmt_expr, [expr, []]],
    [stmt_crate_directive, n_stmt_crate_directive, [crate_directive]]]];

#r[no_box, noop, noop, initializer, n_initializer,
   [[op,   [l_init_op]], [expr, expr]]];

#r[do_box, ensp, desp, local, n_local,
   [[ty,   ty],
    [pat,  pat],
    [init, [opt, initializer]],
    [id,   []]]];

#a[do_box, ensp, desp, decl,
   [[decl_local, n_decl_local, [[seq, local]]],
    [decl_item, n_decl_item, [item]]]];

#r[no_box, noop, noop, arm, n_arm,
   [[pats, [seq, pat]],
    [body, blk]]];

#r[no_box, ensp, desp, field, n_field,
   [[mut,   [l_mutability]],
    [ident, [l_ident]],
    [expr,  expr]]];

#r[do_box, noop, noop, expr, n_expr,
   [[id, []],
    [node, expr_],
    [span, [[]]]]];

#a[no_box, noop, noop, expr_,
   [[expr_vec, n_expr_vec, [[seq, expr], [l_mutability], [l_seq_kind]]],
    [expr_rec, n_expr_rec, [[seq, field], [opt, expr]]],
    [expr_call, n_expr_call, [expr, [seq, expr]]],
    [expr_self_method, n_expr_self_method, [[l_ident]]],
    [expr_bind, n_expr_bind, [expr, [seq, [opt, expr]]]],
    [expr_spawn, n_expr_spawn, 
     [[l_spawn_dom], [l_optional_string], expr, [seq, expr]]],
    [expr_binary, n_expr_binary, [[l_binop], expr, expr]],
    [expr_unary, n_expr_unary, [[l_unop], expr]],
    [expr_lit, n_expr_lit, [lit]],
    [expr_cast, n_expr_cast, [expr, ty]],
    [expr_if, n_expr_if, [expr, blk, [opt, expr]]],
    [expr_ternary, n_expr_ternary, [expr, expr, expr]],
    [expr_while, n_expr_while, [expr, blk]],
    [expr_for, n_expr_for, [local, expr, blk]],
    [expr_for_each, n_expr_for_each, [local, expr, blk]],
    [expr_do_while, n_expr_do_while, [blk, expr]],
    [expr_alt, n_expr_alt, [expr, [seq, arm]]],
    [expr_fn, n_expr_fn, [_fn]],
    [expr_block, n_expr_block, [blk]],
    [expr_move, n_expr_move, [expr, expr]],
    [expr_assign, n_expr_assign, [expr, expr]],
    [expr_swap, n_expr_swap, [expr, expr]],
    [expr_assign_op, n_expr_assign_op, [[l_binop], expr, expr]],
    [expr_send, n_expr_send, [expr, expr]],
    [expr_recv, n_expr_recv, [expr, expr]],
    [expr_field, n_expr_field, [expr, [l_ident]]],
    [expr_index, n_expr_index, [expr, expr]],
    [expr_path, n_expr_path, [[l_path]]],
    [expr_fail, n_expr_fail, [[opt, expr]]],
    [expr_break, n_expr_break, []],
    [expr_cont, n_expr_cont, []],
    [expr_ret, n_expr_ret, [[opt, expr]]],
    [expr_put, n_expr_put, [[opt, expr]]],
    [expr_be, n_expr_be, [expr]],
    [expr_log, n_expr_log, [[l_int], expr]],
    [expr_assert, n_expr_assert, [expr]],
    [expr_check, n_expr_check, [[l_check_mode], expr]],
    [expr_if_check, n_expr_if_check, [expr, blk, [opt, expr]]],
    [expr_port, n_expr_port, [ty]],
    [expr_chan, n_expr_chan, [expr]],
    [expr_anon_obj, n_expr_anon_obj, [anon_obj]]]
   //TODO: expr_uniq, expr_tup
  ];

#a[no_box, ensp, desp, lit,
   [[lit_str, n_lit_str, [[l_str], [l_seq_kind]]],
    [lit_char, n_lit_char, [[l_char]]],
    [lit_int, n_lit_int, [[l_int]]],
    [lit_uint, n_lit_uint, [[l_uint]]],
    [lit_mach_int, n_lit_mach_int, [[l_ty_mach], [l_int]]],
    [lit_float, n_lit_float, [[l_str]]],
    [lit_mach_float, n_lit_mach_float, [[l_ty_mach], [l_str]]],
    [lit_nil, n_lit_nil, []],
    [lit_bool, n_lit_bool, [[l_bool]]]]];

#r[no_box, noop, noop, mt, n_mt,
   [[ty, ty], [mut, [l_mutability]]]];

#r[no_box, ensp, desp, ty_field, n_ty_field,
   [[ident, [l_ident]], [mt, mt]]];

#r[no_box, ensp, desp, ty_arg, n_ty_arg,
   [[mode, [l_mode]], [ty, ty]]];

#r[no_box, ensp, desp, ty_method, n_ty_method,
   [[proto, [l_proto]],
    [ident, [l_ident]],
    [inputs, [seq, ty_arg]],
    [output, ty],
    [cf, [l_controlflow]],
    [constrs, [seq, constr]]]];

#a[do_box, ensp, desp, ty,
   [[ty_nil, n_ty_nil, []],
    [ty_bool, n_ty_bool, []],
    [ty_int, n_ty_int, []],
    [ty_uint, n_ty_uint, []],
    [ty_float, n_ty_float, []],
    [ty_machine, n_ty_machine, [[l_ty_mach]]],
    [ty_char, n_ty_char, []],
    [ty_str, n_ty_str, []],
    [ty_istr, n_ty_istr, []],
    [ty_box, n_ty_box, [mt]],
    [ty_vec, n_ty_vec, [mt]],
    [ty_ivec, n_ty_ivec, [mt]],
    [ty_ptr, n_ty_ptr, [mt]],
    [ty_task, n_ty_task, []],
    [ty_port, n_ty_port, [ty]],
    [ty_chan, n_ty_chan, [ty]],
    [ty_rec, n_ty_rec, [[seq, ty_field]]],
    [ty_fn, n_ty_fn,
     [[l_proto], [seq, ty_arg], ty, [l_controlflow], [seq, constr]]],
    [ty_obj, n_ty_obj, [[seq, ty_method]]],
    [ty_path, n_ty_path, [[l_path], []]],
    [ty_type, n_ty_type, []],
    [ty_constr, n_ty_constr, [ty, [seq, ty_constr]]]]];

/* these four are expanded from the type-parametric code in ast.rs */

type carg_uint = spanned[constr_arg_general_[uint]];
type card_path = spanned[constr_arg_general_[path]];

#a[do_box, ensp, desp, carg_uint
   [[carg_base, n_carg_base, []],
    [carg_ident, n_carg_ident, [[l_uint]]],
    [carg_lit, n_carg_lit, [lit]]]];
#a[do_box, ensp, desp, carg_path,
   [[carg_base, n_carg_base, []],
    [carg_ident, n_carg_ident, [[l_path]]],
    [carg_lit, n_carg_lit, [lit]]]];
#r[do_box, ensp, desp, constr, n_constr,
   [[path, [l_path]],
    [args, [seq, carg_uint]],
    [id, []]]];
#r[do_box, ensp, desp, ty_constr, n_ty_constr_theactualconstraint,
   [[path, [l_path]],
    [args, [seq, carg_path]],
    [id, []]]];


#r[no_box, noop, noop, arg, n_arg,
   [[mode, [l_mode]],
    [ty, ty],
    [ident, [l_ident]],
    [id, []]]];

#r[no_box, noop, noop, fn_decl, n_fn_decl,
   [[inputs, [seq, arg]],
    [output, ty],
    [purity, [l_purity]],
    [il, [l_inlineness]],
    [cf, [l_controlflow]],
    [constraints, [seq, constr]]]];

#r[no_box, noop, noop, _fn, n__fn,
   [[decl, fn_decl],
    [proto, [l_proto]],
    [body, blk]]];

#r[do_box, ensp, desp, method, n_method,
   [[ident, [l_ident]],
    [meth, _fn],
    [id, []]]];

#r[no_box, noop, noop, obj_field, n_obj_field,
   [[mut, [l_mutability]],
    [ty, ty],
    [ident, [l_ident]],
    [id, []]]];

#r[no_box, noop, noop, anon_obj_field, n_anon_obj_field,
   [[mut, [l_mutability]],
    [ty, ty],
    [expr, expr],
    [ident, [l_ident]],
    [id, []]]];

#r[no_box, noop, noop, _obj, n__obj,
   [[fields, [seq, obj_field]],
    [methods, [seq, method]]]];

#r[no_box, noop, noop, anon_obj, n_anon_obj,
   [[fields, [opt, [seq, anon_obj_field])]],
    [methods, [seq, method]],
    [inner_obj, [opt, expr]]];

#r[no_box, noop, noop, _mod, n__mod,
   [[view_items, [seq, view_item]],
    [items, [seq, item]]]];

#r[no_box, noop, noop, native_mod, n_native_mod,
   [[native_name, [l_str]],
    [abi, [l_native_abi]],
    [view_items, [seq, view_item]],
    [items, [seq, native_item]]]];

#r[no_box, noop, noop, variant_arg, n_variant_arg,
   [[ty, ty],
    [id, []]]];

#r[no_box, ensp, desp, variant, n_variant,
   [[name, [l_str]],
    [args, [seq, variant_arg]],
    [id, []]]];

#a[do_box, ensp, desp, view_item,
   [[view_item_use, n_view_item_use,
     [[l_ident], [seq, meta_item], []]],
    [view_item_import, n_view_item_import,
     [[l_ident], [l_seq_ident], []]],
    [view_item_import_glob, n_view_item_import_glob,
     [[l_seq_ident], []]],
    [view_item_export, n_view_item_export,
     [[l_ident], []]]]];

#r[no_box, ensp, desp, attribute, n_attribute,
   [[style, [l_attr_style]],
    [value, meta_item]]];

/* item and native_item have large enough wrappers that their underscored
components get separate handling */

#r[do_box, noop, noop, item, n_item,
   [[ident, [l_ident]],
    [attrs, [seq, attribute]],
    [id, []],
    [node, item_],
    [span, [[]]]]];

   #a[no_box, noop, noop, item_,
      [[item_const, n_item_const, [ty, expr]],
       [item_fn, n_item_fn, [_fn, [l_seq_ty_param]]],
       [item_mod, n_item_mod, [_mod]],
       [item_native_mod, n_item_native_mod,
        [native_mod]],
       [item_ty, n_item_ty, [ty, [l_seq_ty_param]]],
       [item_tag, n_item_tag,
        [[seq, variant], [l_seq_ty_param]]],
       [item_obj, n_item_obj,
        [_obj, [l_seq_ty_param], []]],
       [item_res, n_item_res,
        [_fn, [], [l_seq_ty_param],
         []]]]];

   #r[do_box, noop, noop, native_item, n_native_item,
      [[ident, [l_ident]],
       [attrs, [seq, attribute]],
       [node, native_item_],
       [id, []],
       [span, [[]]]]];

   #a[no_box, noop, noop, native_item_,
      [[native_item_ty, n_native_item_ty, []],
       [native_item_fn, n_native_item_fn,
        [[l_optional_string], fn_decl, 
         [l_seq_ty_param]]]]];
