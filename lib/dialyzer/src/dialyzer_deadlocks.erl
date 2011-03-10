%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2010-2011. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%

%%%----------------------------------------------------------------------
%%% File    : dialyzer_deadlocks.erl
%%% Author  : Maria Christakis <christakismaria@gmail.com>
%%% Description : Utility functions for deadlock detection
%%%
%%% Created : 30 Jan 2010 by Maria Christakis <christakismaria@gmail.com>
%%%----------------------------------------------------------------------
-module(dialyzer_deadlocks).

%% Deadlock Analysis

-export([store_call/6, deadlock/1]).

-export_type([dls/0]).

-include("dialyzer.hrl").

%%% ===========================================================================
%%%
%%%  Local Types
%%%
%%% ===========================================================================

-record(dl, {mfa1      :: mfa(),
             mfa2      :: mfa(),
             args      :: [dialyzer_races:core_vars()],
             arg_types :: [erl_types:erl_type()],
             state     :: _, %% XXX: recursive
             file_line :: file_line()}).

%%% ===========================================================================
%%%
%%%  Exported Types
%%%
%%% ===========================================================================

-type dls() :: [#dl{}].

%%% ===========================================================================
%%%
%%%  Deadlock Analysis
%%%
%%% ===========================================================================

-spec store_call(mfa_or_funlbl(), [erl_types:erl_type()],
                 [dialyzer_races:core_vars()], file_line(),
                 mfa_or_funlbl(), dialyzer_dataflow:state()) ->
      dialyzer_dataflow:state().

store_call(InpFun, InpArgTypes, InpArgs, {File, Line}, CurrFun, InpState) ->
  {Fun, _ArgTypes, _Args, State} =
    dialyzer_races:translate(InpFun, InpArgTypes, InpArgs, InpState, CurrFun),
  AddTag =
    case InpFun of
      {gen_server, call, 2} -> true;
      {gen_server, call, 3} ->
        Timeout = lists:nth(3, InpArgTypes),
        Infinity = erl_types:t_atom('infinity'),
        Infinity =:= Timeout;
      {gen_server, multi_call, 2} -> true;
      {gen_server, multi_call, 3} -> true;
      _Other -> false
    end,
  case AddTag of
    true ->
      CleanState = dialyzer_dataflow:state__records_only(State),
      state__renew_tags(#dl{mfa1 = InpFun, mfa2 = Fun,
                            args = InpArgs, arg_types = InpArgTypes,
                            state = CleanState,
                            file_line = {File, Line}},
                        State);
    false -> State
  end.

-spec deadlock(dialyzer_dataflow:state()) -> dialyzer_dataflow:state().

deadlock(State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Digraph = dialyzer_callgraph:get_digraph(Callgraph),
  Tags = dialyzer_callgraph:get_deadlocks(Callgraph),
  warn_about_cycles(Tags, Digraph, State).

warn_about_cycles([], _Digraph, State) ->
  State;
warn_about_cycles([#dl{mfa2 = MFA} = Tag|Tags], Digraph, State) ->
  {NewTags, NewState} =
    case digraph:get_cycle(Digraph, MFA) of
      false -> {Tags, State};
      [MFA|_SyncMFAs] ->
        {Tags, dialyzer_dataflow:state__add_warning(get_dl_warn(Tag), State)}
    end,
  warn_about_cycles(NewTags, Digraph, NewState).

%%% ===========================================================================
%%%
%%%  Utilities
%%%
%%% ===========================================================================

state__renew_tags(Tag, State) ->
  Callgraph = dialyzer_dataflow:state__get_callgraph(State),
  Tags = dialyzer_callgraph:get_deadlocks(Callgraph),
  NewTags = [Tag|Tags],
  NewCallgraph = dialyzer_callgraph:put_deadlocks(NewTags, Callgraph),
  dialyzer_dataflow:state__put_callgraph(NewCallgraph, State).

%%% ===========================================================================
%%%
%%%  Warning Format Utilities
%%%
%%% ===========================================================================

get_dl_warn(#dl{mfa1 = MFA, args = Args, arg_types = ArgTypes,
                state = CleanState, file_line = FileLine}) ->
  {M, F, _A} = MFA,
  Arguments = dialyzer_dataflow:format_args(Args, ArgTypes, CleanState),
  {?WARN_DEADLOCK, FileLine, {deadlock, [M, F, Arguments]}}.
