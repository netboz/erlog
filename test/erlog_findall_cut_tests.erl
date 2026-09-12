-module(erlog_findall_cut_tests).

-include_lib("eunit/include/eunit.hrl").
-include("../src/erlog_int.hrl").

generator_cut_prunes_its_alternatives_test() ->
    ?assertEqual([1], collect(cut_generator(), false)).

generator_without_cut_keeps_all_alternatives_test() ->
    ?assertEqual([1, 2, 3], collect(
      {';', choices(), {'=', {'X'}, 3}}, false)).

bare_cut_still_reaches_collector_test() ->
    {succeed, Final} = prove({findall, value, '!', {'L'}}, false),
    ?assertEqual([value], value('L', Final)),
    ?assertEqual([], (Final#est.db)#db.loc).

alternatives_after_cut_are_not_pruned_test() ->
    ?assertEqual([1, 2], collect({',', '!', choices()}, false)).

cut_then_failure_returns_empty_collection_test() ->
    ?assertEqual([], collect({',', cut_generator(), fail}, false)).

generator_cut_does_not_prune_callers_alternative_test() ->
    Goal = {findall, {'L'},
            {';', {findall, {'X'}, cut_generator(), {'L'}},
                   {'=', {'L'}, caller}}, {'All'}},
    {succeed, Final} = prove(Goal, false),
    ?assertEqual([[1], caller], value('All', Final)),
    ?assertEqual([], (Final#est.db)#db.loc).

nested_collectors_keep_distinct_cut_boundaries_test() ->
    Inner = {findall, {'X'}, cut_generator(), {'L'}},
    Goal = {findall, {'L'},
            {';', {',', Inner, '!'}, {'=', {'L'}, discarded}}, {'All'}},
    {succeed, Final} = prove(Goal, false),
    ?assertEqual([[1]], value('All', Final)).

call_cut_is_local_to_call_inside_generator_test() ->
    Goal = {';', {call, {',', choices(), '!'}}, {'=', {'X'}, 3}},
    ?assertEqual([1, 3], collect(Goal, false)).

once_cut_is_local_to_once_inside_generator_test() ->
    Goal = {';', {once, {',', choices(), '!'}}, {'=', {'X'}, 3}},
    ?assertEqual([1, 3], collect(Goal, false)).

negation_cut_is_local_to_negation_inside_generator_test() ->
    Goal = {';',
            {',', {'\\+', {',', '!', fail}}, {'=', {'X'}, 1}},
            {'=', {'X'}, 3}},
    ?assertEqual([1, 3], collect(Goal, false)).

meta_goal_boundaries_test_() ->
    X = {'X'}, FailedCut = {',', '!', fail}, GoodCut = {',', '!', true},
    Cases = [
      {negation_failed_cut, {',', {'\\+', FailedCut}, {'=', X, yes}}, {value, yes}},
      {negation_successful_cut, {',', {'\\+', GoodCut}, {'=', X, no}}, fail},
      {if_failed_cut_else, {';', {'->', FailedCut, {'=', X, then}}, {'=', X, otherwise}}, {value, otherwise}},
      {if_successful_cut_then, {';', {'->', GoodCut, {'=', X, then}}, {'=', X, otherwise}}, {value, then}},
      {once_failed_cut_keeps_caller, {';', {',', {once, FailedCut}, {'=', X, then}}, {'=', X, otherwise}}, {value, otherwise}},
      {once_successful_cut, {',', {once, GoodCut}, {'=', X, yes}}, {value, yes}},
      {call_failed_cut_keeps_caller, {';', {',', {call, FailedCut}, {'=', X, then}}, {'=', X, otherwise}}, {value, otherwise}},
      {call_successful_cut, {',', {call, GoodCut}, {'=', X, yes}}, {value, yes}},
      {nested_condition_failed_inner_cut,
       {';', {'->', {';', {'->', FailedCut, fail}, true}, {'=', X, then}}, {'=', X, otherwise}}, {value, then}},
      {failed_condition_without_cut,
       {';', {'->', fail, {'=', X, then}}, {'=', X, otherwise}}, {value, otherwise}}
    ],
    [{atom_to_list(Kind) ++ ":" ++ atom_to_list(Name),
      fun() -> check_meta_boundary(Kind, Goal, Expected) end}
     || Kind <- [inline, clause], {Name, Goal, Expected} <- Cases].

check_meta_boundary(Kind, Goal, Expected) ->
    {ok, Engine0} = erlog:new(),
    {Engine, Query} = case Kind of
        inline -> {Engine0, Goal};
        clause ->
            {{succeed, _}, Defined} = erlog:prove(
                {assertz, {':-', {probe, {'X'}}, Goal}}, Engine0),
            {Defined, {probe, {'X'}}}
    end,
    Observed = case erlog:prove(Query, Engine) of
        {{succeed, Bindings}, _} -> {value, proplists:get_value('X', Bindings)};
        {fail, _} -> fail
    end,
    ?assertEqual(Expected, Observed).

cut_before_failure_still_prunes_later_clauses_test_() ->
    [{atom_to_list(Tail), fun() ->
        {ok, Engine0} = erlog:new(),
        Body = case Tail of
            plain -> {',', '!', fail};
            unreachable_cut -> {',', '!', {',', fail, '!'}}
        end,
        {{succeed, _}, Engine1} = erlog:prove({assertz, {':-', probe, Body}}, Engine0),
        {{succeed, _}, Engine2} = erlog:prove({assertz, probe}, Engine1),
        ?assertMatch({fail, _}, erlog:prove(probe, Engine2))
    end} || Tail <- [plain, unreachable_cut]].

generator_bindings_do_not_escape_test() ->
    Goal = {',', {findall, {'X'}, cut_generator(), {'L'}}, {var, {'X'}}},
    {succeed, Final} = prove(Goal, false),
    ?assertEqual([1], value('L', Final)).

ordinary_generator_keeps_staged_writes_test() ->
    Goal = {findall, {'X'},
            {',', {assertz, generator_write}, cut_generator()}, {'L'}},
    {succeed, Final} = prove(Goal, false),
    ?assertEqual([1], value('L', Final)),
    ?assert(has_fact(generator_write, Final)).

checkpointed_generator_restores_writes_after_cut_test() ->
    Goal = {',', {assertz, caller_write},
            {findall, {'X'},
             {',', {assertz, generator_write}, cut_generator()}, {'L'}}},
    {succeed, Final} = prove(Goal, true),
    ?assertEqual([1], value('L', Final)),
    ?assert(has_fact(caller_write, Final)),
    ?assertNot(has_fact(generator_write, Final)),
    ?assertEqual(0, Final#est.checkpoint_depth),
    ?assertEqual([], (Final#est.db)#db.loc).

checkpointed_cut_failure_restores_generator_writes_test() ->
    Goal = {findall, {'X'},
            {',', {assertz, generator_write}, {',', cut_generator(), fail}},
            {'L'}},
    {succeed, Final} = prove(Goal, true),
    ?assertEqual([], value('L', Final)),
    ?assertNot(has_fact(generator_write, Final)).

generator_error_after_cut_cleans_collector_test() ->
    Goal = {findall, {'X'},
            {',', cut_generator(), {call, 42}}, {'L'}},
    {erlog_error, {type_error, callable, 42}, Failed} =
        catch erlog_int:prove_goal(Goal, state()),
    ?assertEqual([], (Failed#est.db)#db.loc),
    {succeed, Final} = erlog_int:prove_goal(
                        {findall, value, '!', {'L'}}, Failed),
    ?assertEqual([value], value('L', Final)),
    ?assertEqual([], (Final#est.db)#db.loc).

choices() -> {';', {'=', {'X'}, 1}, {'=', {'X'}, 2}}.

cut_generator() ->
    {';', {',', choices(), '!'}, {'=', {'X'}, 3}}.

collect(Generator, Checkpoints) ->
    {succeed, Final} = prove({findall, {'X'}, Generator, {'L'}}, Checkpoints),
    value('L', Final).

prove(Goal, false) -> erlog_int:prove_goal(Goal, state());
prove(Goal, true) ->
    Initial = erlog_int:enter_choicepoint_checkpoints(state()),
    {Result, Final} = erlog_int:prove_goal(Goal, Initial),
    {Result, erlog_int:leave_choicepoint_checkpoints(Final)}.

state() ->
    {ok, St} = erlog_int:new(erlog_db_dict, null),
    Db = lists:foldl(fun(Mod, Acc) -> Mod:load(Acc) end,
                    St#est.db, [erlog_bips, erlog_lib_dcg, erlog_lib_lists]),
    St#est{db=Db}.

value(Name, #est{bs=Bs}) -> erlog_int:dderef({Name}, Bs).

has_fact(Fact, #est{db=#db{mod=Mod,ref=Ref}}) ->
    case Mod:get_procedure(Ref, erlog_int:functor(Fact)) of
        {clauses, Clauses} ->
            lists:any(fun({_Tag, Head, _Body}) -> Head =:= Fact end, Clauses);
        _ -> false
    end.
