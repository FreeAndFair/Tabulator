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

package Coq_Types
  -- The Coq types involved in the Tabulator.
is
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
end Coq_Types;
