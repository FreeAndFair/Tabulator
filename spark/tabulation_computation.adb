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

package body Tabulation_Computation is
   function Sum_of_Choices
     (Tally: Plurality_Tally)
      return Natural
   is
      Result: Natural;
   begin
      Result := 0;
      for Choice in Tally'Range loop
         Result := Result + Tally (Choice);
      end loop;
      return Result;
   end Sum_of_Choices;
   
   function Plurality_Tabulation_Algorithm
     (The_Tabulator: in out Tabulator;
      A_Contest: in Contest)
      return Simple_Plurality_Contest_Result
   is
      Result: Simple_Plurality_Contest_Result;
      Tally: Plurality_Tally (No_Choice .. Max_Choices);
      A_Winner: Choice;
      A_Tie: Boolean;
   begin
      Tally := (others => 0);
      A_Winner := 1;
      A_Tie := False;
      -- Sum up votes for each choice.
      for Choice in Positive range 1 .. A_Contest.Total_Choices loop
         Tally (Choice) := Tally (Choice) + 1;
      end loop;
      -- Determine a choice that has the most votes.
      for Choice in Positive range 1 .. A_Contest.Total_Choices loop
         if Tally (Choice) > Tally (A_Winner) then
            A_Winner := Choice;
         end if;
      end loop;
      -- Determine if there is a tie.
      for Choice in Positive range 1 .. A_Contest.Total_Choices loop
         if Choice /= A_Winner and then Tally (Choice) = Tally (A_Winner) then
            A_Tie := True;
         end if;
      end loop;
      if A_Tie then
         Result := (The_Winner  => No_Choice,
                    Tally       => Tally,
                    The_Contest => A_Contest);
      else
         Result := (The_Winner  => A_Winner,
                    Tally       => Tally,
                    The_Contest => A_Contest);
      end if;
      return Result;
   end  Plurality_Tabulation_Algorithm;

--   function Plurality_Tabulation_Algorithm
--     (The_Tabulator: in out Tabulator;
--      A_Contest: in Contest)
--      return Multiseat_Plurality_Contest_Result
end Tabulation_Computation;

