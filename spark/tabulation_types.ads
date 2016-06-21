------------------------------------------------------------------------------
-- (C) Free & Fair
------------------------------------------------------------------------------
--
-- The Free & Fair Tabulator is free software.
--
-- redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
-- * Redistributions of source code must retain the above copyright notice, this
--   list of conditions and the following disclaimer.
--
-- * Redistributions in binary form must reproduce the above copyright notice,
--   this list of conditions and the following disclaimer in the documentation
--   and/or other materials provided with the distribution.
--
-- * Neither the names of the copyright holders nor the names of its
--   contributors may be used to endorse or promote products derived from
--   this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
-- FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
-- DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
-- OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--==============================================================================

pragma SPARK_Mode(On);

with Tabulation_Constants; use Tabulation_Constants;

package Tabulation_Types
-- The types involved in the Tabulator.
is
   -- Tabulation algorithms potentially supported by the tabulator.
   type Voting_Method is (Plurality, Rcv, Approval, San_Francisco_Rcv);
   -- RCV variants, in particular.
   subtype Rcv_Voting_Method is Voting_Method range Rcv .. San_Francisco_Rcv;

   -- Plurality cast vote records (CVRs).  

   -- The digital representation of a single contest on a ballot.
   -- We support up to Max_Choices choices per contest.
   subtype Choice is Natural range No_Choice .. Max_Choices;
   -- A type encoding the maximal range of ballot indices.
   subtype Ballot_Range is Natural range 0 .. Max_Ballots;
   -- A list of choices, as a slice of the ballots in a contest.
   type Choices is array(Ballot_Range) of Choice;
   -- A ballot is a list of choices.
   type Ballot is array(Positive range 1 .. Max_Contests) of Choice;
   -- A list ballots. No more than Max_Contests contests are permitted.
   type Ballots is array(Ballot_Range) of Ballot;
   
   -- An empty list of choices used as a placeholder during creation.
   Empty_Choices: constant Choices := (others => No_Choice);
   -- An empty ballot used as a placeholder during creation.
   Empty_Ballot: constant Ballot := (others => No_Choice);
     
   -- A single election contest. A contest, consisting of a voting
   -- method and some choices.  Note the function Contest_Invariant.
   -- The Max_Choices parameter of this discriminated record encodes
   -- the query "How many choices are actually available in this contest?"
   type Contest is
      record
         -- What kind of election scheme does this contest have?
         The_Voting_Method: Voting_Method;
         -- What is the list of choices for this contest?
         Some_Choices:      Choices;
         -- How many choices are there for this particular contest?
         Total_Choices:     Choice;
         -- How many ballots are in this contest?
         Total_Ballots:     Ballot_Range;
      end record;
   
   -- An empty contest used as a placeholder during creation.
   Empty_Contest: constant Contest := 
     (The_Voting_Method => Plurality,
      Some_Choices      => Empty_Choices,
      Total_Choices     => No_Choice,
      Total_Ballots     => 0);
        
   -- A contest result. Contest results are computed by one of the
   -- Tabulation_Algorithm functions in the Tabulation_Computation
   -- package. This is a tagged record so that we can extend it
   -- appropriately for various kinds of election schemes.
   -- @design kiniry - Should this be a subtype of Contest?
   type Contest_Result is tagged
      record
         -- This is the result of which contest?
         The_Contest: Contest;
      end record;
   
   -- An empty contest result used as a placeholder during creation.
   Empty_Contest_Result: constant Contest_Result :=
     (The_Contest => Empty_Contest);
   
   -- The result of a plurality tally.
   type Plurality_Tally is array(Choice range <>) of Natural;
     
   -- A plurality election result with a single winner.  
   -- @review kiniry - Is this record type redundant and we should
   -- only define and use Multiseat_Plurality_Contest_Result, renaming
   -- it Plurality_Contest_Result and for a simple plurality election
   -- the cardinality of Winners will be 1?
   -- @design kiniry - Ties have no winner.
   type Simple_Plurality_Contest_Result is new Contest_Result with
      record
         -- How many votes did each choice receive?
         Tally:      Plurality_Tally (No_Choice .. Max_Choices);
         -- Who is the single winner of this contest?
         The_Winner: Choice;
      end record;
   
   -- Types encoding unordered and ordered choices used in multi-seat contests.
   type Unordered_Choices is 
     array(Positive range No_Choice .. Max_Choices) of Choice;
   type Ordered_Choices is 
     array(Positive range No_Choice .. Max_Choices) of Choice;
   
   -- A plurality election result with multiple winners.
   -- @design kiniry - State the invariant relating Winners to The_Winner.
   type Multiseat_Plurality_Contest_Result is 
     new Simple_Plurality_Contest_Result with
      record
         -- Who are the winners of this contest?
         The_Winners: Unordered_Choices;
      end record;
   
   -- A multiseat RCV election result with one or more winners.
   -- @design kiniry - Note the lack of alignment with this definition and 
   -- that of Simple_Plurality_Contest_Result.
   type Multiseat_Rcv_Contest_Result is new Contest_Result with
      record
         -- Who are the winners of this contest?
         The_Winners: Ordered_Choices;
      end record;
   
end Tabulation_Types;       
