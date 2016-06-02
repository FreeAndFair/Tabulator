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

package Tabulation_Computation
  -- Computational concepts associated with tabulation.  Typically sets
  -- of ballots are tabulated to determine winning candidates or an answer
  -- to a ballot question.
is
   -- The tabulating engine. The main data structure tying together
   -- all inputs to the tabulating engine. The engine that concretizes
   -- the input and tabulation of votes to produce results for a
   -- variety of voting methods.
   -- @bon kiniry - Note that this class resides in the
   -- TABULATION_ROOT cluster in the architecture but because of
   -- SPARK's typesystem we must declare this record here and expose
   -- its queries in Tabulation_Root.
   type Tabulator is
      record
         The_Voting_Method:  Voting_Method;
         A_Contest:          Contest;
         A_Contest_Result:   Contest_Result;
      end record;
   
   -- A function that tabulates according to a specific election
   -- method.  What is the result of tabulating this contest using the
   -- appropriate voting method?
   function Tabulation_Algorithm (The_Tabulator: in Tabulator;
                                  A_Contest: in Contest)
     return Contest_Result;
     
   -- Tabulation of the plurality voting method.  What is the result
   -- of tabulating this contest using a plurality voting method?
   function Plurality_Tabulation_Algorithm (The_Tabulator: in Tabulator;
                                            A_Contest: in Contest)
     return Contest_Result;
   
   -- A tabulator for all RCV voting methods.  What is the result of
   -- tabulating this contest using an RCV voting method?
   -- @design kiniry - Is this function necessary at all?
   function Rcv_Tabulation_Algorithm (The_Tabulator: in Tabulator;
                                      A_Contest: in Contest)
     return Contest_Result;
     
   -- A tabulator for San Francisco County and City's version of an
   -- RCV method. What is the result of tabulating this contest using
   -- the San Francisco's variant of the RCV voting method?
   function San_Francisco_Rcv_Tabulation_Algorithm (The_Tabulator: in Tabulator;
                                                    A_Contest: in Contest)
     return Contest_Result;
     
   -- A tabulator for an approval voting method.  What is the result
   -- of tabulating this contest using an approval voting method?
   function Approval_Tabulation_Algorithm (The_Tabulator: in Tabulator;
                                           A_Contest: in Contest)
     return Contest_Result;
end Tabulation_Computation;
