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

package body Tabulation_Computation is
   
   function Tabulator_Contest_Agreement (A_Tabulator: in Tabulator;
                                         A_Contest: in Contest)
      return Boolean
   is (A_Tabulator.The_Voting_Method = A_Contest.The_Voting_Method);
                                         
   function Tabulation_Algorithm (The_Tabulator: in out Tabulator;
                                  A_Contest: in Contest)
      return Contest_Result
   is
   begin
      The_Tabulator.A_Contest := A_Contest;
      return (case A_Contest.The_Voting_Method is
                 when Plurality =>
                    Plurality_Tabulation_Algorithm (The_Tabulator, A_Contest),
                 when Rcv =>
                    Rcv_Tabulation_Algorithm (The_Tabulator, A_Contest),
                 when Approval =>
                    Approval_Tabulation_Algorithm (The_Tabulator, A_Contest),
                 when San_Francisco_Rcv =>
                    San_Francisco_Rcv_Tabulation_Algorithm (The_Tabulator, A_Contest));
   end Tabulation_Algorithm;

   function Plurality_Tabulation_Algorithm (The_Tabulator: in out Tabulator;
                                            A_Contest: in Contest)
      return Simple_Plurality_Contest_Result
   is
      Result: Simple_Plurality_Contest_Result;
      Tally: array(1 .. A_Contest.Max_Choices) of Integer;
   begin
      pragma Assert(False);
      Result := (The_Contest => A_Contest,
                 The_Winner => 1);
      return Result;
   end  Plurality_Tabulation_Algorithm;
      
   function Rcv_Tabulation_Algorithm (The_Tabulator: in out Tabulator;
                                      A_Contest: in Contest)
      return Contest_Result
   is
      Result: Contest_Result;
   begin
      pragma Assert(False);
      Result := (The_Contest => A_Contest);
      return Result;
   end Rcv_Tabulation_Algorithm;

   function San_Francisco_Rcv_Tabulation_Algorithm (The_Tabulator: in Tabulator;
                                                    A_Contest: in Contest)
      return Contest_Result
   is
      Result: Contest_Result;
   begin
      pragma Assert(False);
      Result := (The_Contest => A_Contest);
      return Result;
   end San_Francisco_Rcv_Tabulation_Algorithm;

   function Approval_Tabulation_Algorithm (The_Tabulator: in Tabulator;
                                           A_Contest: in Contest)
      return Contest_Result
   is
      Result: Contest_Result;
   begin
      pragma Assert(False);
      Result := (The_Contest => A_Contest);
      return Result;
   end Approval_Tabulation_Algorithm;
end Tabulation_Computation;

