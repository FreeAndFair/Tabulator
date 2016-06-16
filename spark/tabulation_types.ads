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

with SPARK.Text_IO; use SPARK.Text_IO;

package Tabulation_Types
  -- The types involved in the Tabulator.
is
   -- Comma separated values (CSVs).
   -- We support values in CSVs of length no greater than 256 bytes.
   -- @review kiniry - Make these kinds of types private. Expose exactly
   -- those types mentioned in the BON specification.
   subtype Index_256 is Integer range 1 .. 256;
   subtype String_256 is String(Index_256);
   -- A single list of comma-separated values.
   type Csv is array(Positive) of String_256;
   -- A list of CSVs.
   type Csvs is array(Positive) of Csv;

   -- Tabulation algorithms potentially supported by the tabulator.
   type Voting_Method is (Plurality, Rcv, Approval, San_Francisco_Rcv);
   -- RCV variants, in particular.
   subtype Rcv_Voting_Method is Voting_Method range Rcv .. San_Francisco_Rcv;

   -- Plurality cast vote records (CVRs).  The digital representation
   -- of a single race on a ballot in a plurality.
   type Cvr is array(Positive) of Natural;
   -- A list of CVRs.
   type Cvrs is array(Positive) of Cvr;
   
   -- ============================================================
   -- Coq types
   -- ============================================================
   -- A Choice in a race; aka a Candidate or a Measure Choice.
   -- @design kiniry - Should these types be private as well?
   -- @design kiniry - Should these kinds of types and functions be
   -- relegated into a child package?
   -- @coq Variable candidate: Set.
   type Choice is new Positive;
   -- A ballot contains a single choice.
   -- @coq Let ballot := candidate.
   type Ballot is new Choice;
   -- An election is a list of Ballots.
   -- @coq Let election := list ballot.
   type Election is array(Positive) of Ballot;

   -- Does this candidate participate in that election?
   -- @design kiniry - Should these functions be private and be used only
   -- for assurance arguments relating this implementation to the Coq spec?
   -- @coq Definition participates candidate (election : election) : Prop
   function Participates (A_Choice: in Choice; An_Election: in Election)
                         return Boolean;
   -- Has this candidate won that election?
   -- @coq Definition hasPlurality winningCandidate (election : election) : Prop 
   function Has_Plurality (A_Choice: in Choice; An_Election: in Election)
                          return Boolean;
   -- ============================================================
   
   -- A single election contest. A contest, consisting of a voting
   -- method and some choices.
   type Contest is
      record
         -- What kind of election scheme does this contest have?
         The_Voting_Method: Voting_Method;
         -- What is the list of choices for this contest?
         Some_Choices: Choice;
      end record;
   -- A contest result. Contest results are computed by one of the
   -- Tabulation_Algorithm functions in the Tabulation_Computation
   -- package. This is a tagged record so that we can extend it
   -- appropriately for various kinds of election schemes.
   type Contest_Result is tagged
      record
         -- This is the result of which contest?
         The_Contest: Contest;
      end record;
   -- A plurality election result with a single winner.  
   -- @review kiniry - Is this record type redundant and we should
   -- only define and use Multiseat_Plurality_Contest_Result, renaming
   -- it Plurality_Contest_Result and for a simple plurality election
   -- the cardinality of Winners will be 1?
   type Simple_Plurality_Contest_Result is new Contest_Result with
      record
         -- Who is the single winner of this contest?
         Winner: Choice;
      end record;
   -- @design kiniry - More private types.
   type Unordered_Choices is array(Positive) of Choice;
   type Ordered_Choices is array(Positive) of Choice;
   -- A plurality election result with multiple winners.
   type Multiseat_Plurality_Contest_Result is new Simple_Plurality_Contest_Result with
      record
         -- Who are the winners of this contest?
         Winners: Unordered_Choices;
      end record;
   -- A multiseat RCV election result with one or more winners.
   -- @design kiniry - Note the lack of alignment with this definition and 
   -- that of Simple_Plurality_Contest_Result.
   type Multiseat_Rcv_Contest_Result is new Contest_Result with
      record
         -- Who are the winners of this contest?
         Winners: Ordered_Choices;
      end record;
   
end Tabulation_Types;       
