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

with Tabulation_Types; use Tabulation_Types;
with Tabulation_Computation; use Tabulation_Computation;

package Tabulation_Root
  -- Main body of tabulation system.
is
   -- The engine that concretizes the input and tabulation of votes to
   -- produce results for a variety of voting methods.


   -- What kind of voting method do you support?
   function Voting_Method (A_Tabulator: in Tabulator)
     return Voting_Method;
   -- What is the result of tabulating this contest with that set of CVRs?
   function Contest_Result (The_Tabulator: in Tabulator;
                            A_Contest: in Contest)
     return Contest_Result;
   -- Create a tabulation algorithm based upon this voting method.
   function Create (A_Voting_Method: Voting_Method) return Tabulator;
   -- Tabulate based upon the following contest specification.
   -- Will read from Argument to determine contest specification.     
   function Tabulate return Contest_Result_File;
     
end Tabulation_Root;
