-module(erlog_deref_tests).
-include_lib("eunit/include/eunit.hrl").
-include("../src/erlog_int.hrl").
-export([capture/3]).

unchanged_terms_keep_their_storage_test() ->
    Bs = erlog_int:new_bindings(),
    Terms = [lists:seq(1, 400), list_to_tuple(lists:seq(1, 400)),
             {nested, [a, {tuple, b, <<"payload">>}], {unbound}},
             [a, b | improper], {}, self(), make_ref(), fun() -> ok end],
    [?assert(erts_debug:same(T, erlog_int:dderef(T, Bs))) || T <- Terms].

resolved_variables_preserve_unmodified_siblings_test() ->
    Shared = lists:seq(1, 400),
    Bs = bindings([{{x}, {y}}, {{y}, {value, Shared}}, {{tail}, Shared}]),
    Input = {root, Shared, {x}, [before|{tail}], {free}},
    Result = erlog_int:dderef(Input, Bs),
    ?assertEqual({root, Shared, {value, Shared}, [before|Shared], {free}}, Result),
    ?assert(erts_debug:same(Shared, element(2, Result))),
    ?assert(erts_debug:same(Shared, element(2, element(3, Result)))),
    ?assert(erts_debug:same(Shared, tl(element(4, Result)))).

variable_aliases_and_opaque_functors_test() ->
    Bs = bindings([{{a}, {b}}, {{b}, {c}}, {{bound}, [1|{a}]}]),
    ?assertEqual({term, {c}, {c}, [1|{c}]},
                 erlog_int:dderef({term, {a}, {b}, {bound}}, Bs)),
    Opaque = {{'$quod_symbol', <<"foreign">>}, {a}, [value|{bound}]},
    ?assertEqual({{'$quod_symbol', <<"foreign">>}, {c}, [value, 1|{c}]},
                 erlog_int:dderef(Opaque, Bs)),
    ?assertThrow({erlog_error, instantiation_error},
                 erlog_int:dderef_list({bound}, Bs)),
    Proper = erlog_int:add_binding({c}, [2, 3], Bs),
    ?assertEqual([1, 2, 3], erlog_int:dderef_list({bound}, Proper)).

changed_tuple_positions_test() ->
    Base = list_to_tuple(lists:seq(1, 80)),
    Bs = bindings([{{x}, resolved}]),
    [?assertEqual(setelement(I, Base, resolved),
                  erlog_int:dderef(setelement(I, Base, {x}), Bs))
     || I <- [1, 2, 40, 79, 80]],
    ?assertEqual({resolved, resolved, resolved},
                 erlog_int:dderef({{x}, {x}, {x}}, Bs)).

host_dispatch_resolves_again_after_backtracking_test() ->
    {ok, St0} = erlog_int:new(erlog_db_dict, null),
    Db = erlog_int:add_compiled_proc({capture, 2}, ?MODULE, capture,
                                   erlog_bips:load(St0#est.db)),
    Alternatives = {';', {'=', {'X'}, first}, {'=', {'X'}, second}},
    Goal = {',', Alternatives, {capture, {nested, [{'X'}]}, {'Answer'}}},
    {succeed, First} = erlog_int:prove_goal(Goal, St0#est{db = Db}),
    ?assertEqual({nested, [first]}, erlog_int:dderef({'Answer'}, First#est.bs)),
    {succeed, Second} = erlog_int:fail(First),
    ?assertEqual({nested, [second]}, erlog_int:dderef({'Answer'}, Second#est.bs)),
    ?assertMatch({fail, _}, erlog_int:fail(Second)),
    {succeed, Cut} = erlog_int:prove_goal({',', Goal, '!'}, St0#est{db = Db}),
    ?assertEqual({nested, [first]}, erlog_int:dderef({'Answer'}, Cut#est.bs)),
    ?assertMatch({fail, _}, erlog_int:fail(Cut)).

capture({capture, {nested, [Value]} = Resolved, Output}, Next, St)
  when is_atom(Value) ->
    erlog_int:unify_prove_body(Output, Resolved, Next, St).

bindings(Pairs) ->
    lists:foldl(fun({Var, Value}, Bs) -> erlog_int:add_binding(Var, Value, Bs) end,
                erlog_int:new_bindings(), Pairs).
