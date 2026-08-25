-module(erlog_opaque_functor_tests).

-include_lib("eunit/include/eunit.hrl").
-include("../src/erlog_int.hrl").

-export([accept_1/3]).

opaque_functor_is_valid_data_inside_a_goal_test() ->
    St0 = state(),
    Db1 = erlog_int:add_compiled_proc(
            {accept, 1}, ?MODULE, accept_1, St0#est.db),
    OpaqueGoal = {{'$quod_symbol', <<"remote_predicate">>}, value, {'X'}},
    {succeed, _} = erlog_int:prove_goal(
                       {accept, OpaqueGoal}, St0#est{db = Db1}).

opaque_functor_is_not_executable_test() ->
    OpaqueGoal = {{'$quod_symbol', <<"remote_predicate">>}, value},
    ?assertMatch(
       {erlog_error, {type_error, callable, _}, _},
       catch erlog_int:prove_goal(OpaqueGoal, state())).

accept_1({accept, _Value}, Next, St) ->
    erlog_int:prove_body(Next, St).

state() ->
    {ok, St0} = erlog_int:new(erlog_db_dict, null),
    Db1 = lists:foldl(fun(Mod, Db) -> Mod:load(Db) end,
                      St0#est.db,
                      [erlog_bips, erlog_lib_dcg, erlog_lib_lists]),
    St0#est{db = Db1}.
