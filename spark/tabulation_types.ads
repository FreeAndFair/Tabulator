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

with SPARK.Text_IO; use SPARK.Text_IO;

package Tabulation_Types
  -- The types involved in the Tabulator.
is
   -- Comma separated values (CSVs).
   -- We support values in CSVs of length no greater than 256 bytes.
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
   type Cvrs is array(Positive) of Cvr;
   -- A CVR file.
   type Cvr_File is
      record
         The_File: File_Type;
         Some_Cvrs: Cvrs;
      end record;

   -- A Choice in a race; aka a Candidate or a Measure Choice.
   -- @coq Variable candidate: Set.
   type Choice is new Positive;
   -- A ballot contains a single choice.
   -- @coq Let ballot := candidate.
   type Ballot is new Choice;
   -- An election is a list of Ballots.
   -- @coq Let election := list ballot.
   type Election is array(Positive) of Ballot;

   -- Does this candidate participate in that election?
   -- @coq Definition participates candidate (election : election) : Prop
   function Participates (A_Choice: Choice; An_Election: Election)
                         return Boolean;
   -- Has this candidate won that election?
   -- @coq Definition hasPlurality winningCandidate (election : election) : Prop 
   function Has_Plurality (A_Choice: Choice; An_Election: Election)
                          return Boolean;

   -- A contest, consisting of a voting method and some choices.
   type Contest is
      record
         -- What kind of election scheme does this contest have?
         The_Voting_Method: Voting_Method;
         -- What is the list of choices for this contest?
         Some_Choices: Choice;
      end record;
   type Contest_Result is tagged
      record
         -- This is the result of which contest?
         The_Contest: Contest;
      end record;
   type Simple_Plurality_Contest_Result is new Contest_Result with
      record
         -- Who is the single winner of this contest?
         Winner: Choice;
      end record;
   type Unordered_Choices is array(Positive) of Choice;
   type Ordered_Choices is array(Positive) of Choice;
   type Multiseat_Plurality_Contest_Result is new Simple_Plurality_Contest_Result with
      record
         -- Who are the winners of this contest?
         Winners: Unordered_Choices;
      end record;
   type Multiseat_Rcv_Contest_Result is new Contest_Result with
      record
         -- Who are the winners of this contest?
         Winners: Ordered_Choices;
      end record;
   
   -- A CSV file.
   type Csv_File is
      record
         The_File: File_Type;
         Some_Csvs: Csvs;
      end record;
   -- A file that contains a description of a single class.
   type Contest_File is
      record
         The_File: File_Type;
         A_Contest: Contest;
      end record;
   -- A file describing a contest result.
   type Contest_Result_File is
      record
         The_File: File_Type;
         A_Contest_Result: Contest_Result;
      end record;

   -- The tabulating engine.
   type Tabulator is
      record
         The_Voting_Method:  Voting_Method;
         A_Contest:          Contest;
         A_Contest_Result:   Contest_Result;
      end record;

end Tabulation_Types;       
