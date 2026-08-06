-module(erlog_choicepoint_checkpoint_tests).

-include_lib("eunit/include/eunit.hrl").
-include("../src/erlog_int.hrl").

-export([with_checkpoints_1/3]).

default_mode_keeps_standard_non_backtrackable_writes_test() ->
    Goal = {';', {',', {assertz, {branch, abandoned}}, fail}, true},
    {succeed, Final} = erlog_int:prove_goal(Goal, state()),
    ?assert(has_fact({branch, abandoned}, Final)).

inherited_checkpoint_mode_survives_fresh_proof_entry_test() ->
    Goal = {';', {',', {assertz, {branch, abandoned}}, fail}, true},
    Inherited = erlog_int:enter_choicepoint_checkpoints(state()),
    {succeed, Final0} = erlog_int:prove_goal(Goal, Inherited),
    Final = erlog_int:leave_choicepoint_checkpoints(Final0),
    ?assertNot(has_fact({branch, abandoned}, Final)).

checkpoint_mode_restores_failed_disjunction_branch_test() ->
    Goal = {';',
            {',', {assertz, {branch, abandoned}}, fail},
            {assertz, {branch, selected}}},
    {succeed, Final} = prove_checkpointed(Goal),
    ?assertNot(has_fact({branch, abandoned}, Final)),
    ?assert(has_fact({branch, selected}, Final)).

write_before_choicepoint_is_retained_test() ->
    Goal = {',',
            {assertz, {prefix, retained}},
            {';',
             {',', {assertz, {branch, abandoned}}, fail},
             {assertz, {branch, selected}}}},
    {succeed, Final} = prove_checkpointed(Goal),
    ?assert(has_fact({prefix, retained}, Final)),
    ?assertNot(has_fact({branch, abandoned}, Final)),
    ?assert(has_fact({branch, selected}, Final)).

retract_and_abolish_are_restored_test() ->
    Initial = clauses([{item, one}, {item, two}, {other, kept}]),
    Goal = {';',
            {',',
             {retract, {item, {'Value'}}},
             {',', {abolish, {'/', other, 1}}, fail}},
            true},
    {succeed, Final0} = erlog_int:prove_goal(
                          {with_checkpoints, Goal}, Initial),
    Final = erlog_int:leave_choicepoint_checkpoints(Final0),
    ?assert(has_fact({item, one}, Final)),
    ?assert(has_fact({item, two}, Final)),
    ?assert(has_fact({other, kept}, Final)).

interpreted_clause_retry_restores_failed_clause_test() ->
    Initial = clauses([
               {':-', choose, {',', {assertz, {chosen, first}}, fail}},
               {':-', choose, {assertz, {chosen, second}}}
              ]),
    {succeed, Final0} = erlog_int:prove_goal(
                          {with_checkpoints, choose}, Initial),
    Final = erlog_int:leave_choicepoint_checkpoints(Final0),
    ?assertNot(has_fact({chosen, first}, Final)),
    ?assert(has_fact({chosen, second}, Final)).

compiled_list_retry_restores_failed_alternative_test() ->
    Goal = {',',
            {member, {'Value'}, [first, second]},
            {',',
             {assertz, {chosen, {'Value'}}},
             {'\\=', {'Value'}, first}}},
    {succeed, Final} = prove_checkpointed(Goal),
    ?assertNot(has_fact({chosen, first}, Final)),
    ?assert(has_fact({chosen, second}, Final)).

cut_discards_checkpoint_without_rolling_back_test() ->
    Goal = {',',
            {member, {'Value'}, [first, second]},
            {',', {assertz, {chosen, {'Value'}}}, '!'}},
    {succeed, Final} = prove_checkpointed(Goal),
    ?assert(has_fact({chosen, first}, Final)),
    ?assertNot(has_fact({chosen, second}, Final)).

failure_reasons_survive_database_restore_test() ->
    Goal = {';',
            {fail_with_reason, rejected_branch},
            {get_fail_reasons, {'Reasons'}}},
    {succeed, Final} = prove_checkpointed(Goal),
    ?assertEqual([rejected_branch], value('Reasons', Final)).

findall_accumulator_survives_generator_backtracking_test() ->
    Goal = {findall, {'Value'},
            {member, {'Value'}, [first, second]}, {'Values'}},
    {succeed, Final} = prove_checkpointed(Goal),
    ?assertEqual([first, second], value('Values', Final)).

findall_generator_writes_are_restored_test() ->
    Goal = {findall, {'Value'},
            {',', {assertz, generator_write},
             {'=', {'Value'}, one}},
            {'Values'}},
    {succeed, Final} = prove_checkpointed(Goal),
    ?assertEqual([one], value('Values', Final)),
    ?assertNot(has_fact(generator_write, Final)).

nested_checkpoint_depth_is_balanced_test() ->
    St0 = state(),
    St1 = erlog_int:enter_choicepoint_checkpoints(St0),
    St2 = erlog_int:enter_choicepoint_checkpoints(St1),
    ?assertEqual(2, St2#est.checkpoint_depth),
    St3 = erlog_int:leave_choicepoint_checkpoints(St2),
    St4 = erlog_int:leave_choicepoint_checkpoints(St3),
    ?assertEqual(0, St4#est.checkpoint_depth).

unsupported_mutable_database_fails_cleanly_test() ->
    Name = erlog_checkpoint_ets_test,
    case ets:whereis(Name) of
        undefined -> ok;
        _ -> ets:delete(Name)
    end,
    try
        {ok, St} = erlog_int:new(erlog_db_ets, Name),
        ?assertMatch(
           {erlog_error,
            {permission_error, enable, choicepoint_checkpoints,
             erlog_db_ets}, _},
           catch erlog_int:enter_choicepoint_checkpoints(St))
    after
        case ets:whereis(Name) of
            undefined -> ok;
            _ -> ets:delete(Name)
        end
    end.

prove_checkpointed(Goal) ->
    case erlog_int:prove_goal({with_checkpoints, Goal}, state()) of
        {succeed, St1} ->
            {succeed, erlog_int:leave_choicepoint_checkpoints(St1)};
        {fail, St1} ->
            {fail, erlog_int:leave_choicepoint_checkpoints(St1)}
    end.

state() ->
    {ok, St0} = erlog_int:new(erlog_db_dict, null),
    Db1 = lists:foldl(fun(Mod, Db) -> Mod:load(Db) end,
                      St0#est.db,
                      [erlog_bips, erlog_lib_dcg, erlog_lib_lists]),
    Db2 = erlog_int:add_compiled_proc(
            {with_checkpoints, 1}, ?MODULE, with_checkpoints_1, Db1),
    St0#est{db=Db2}.

with_checkpoints_1({with_checkpoints, Goal}, Next, St) ->
    erlog_int:prove_body(
      [{call, Goal} | Next], erlog_int:enter_choicepoint_checkpoints(St)).

clauses(Clauses) ->
    St = state(),
    Db = lists:foldl(fun erlog_int:assertz_clause/2,
                     St#est.db, Clauses),
    St#est{db=Db}.

has_fact(Fact, #est{db=#db{mod=DbMod,ref=DbRef}}) ->
    case DbMod:get_procedure(DbRef, erlog_int:functor(Fact)) of
        {clauses, Clauses} ->
            lists:any(fun({_Tag, Head, _Body}) -> Head =:= Fact end,
                      Clauses);
        _ ->
            false
    end.

value(Name, #est{bs=Bs}) ->
    erlog_int:dderef({Name}, Bs).
