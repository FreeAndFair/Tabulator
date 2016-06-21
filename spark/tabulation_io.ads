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
with Tabulation_Types; use Tabulation_Types;

package Tabulation_IO
  -- The input and output artifacts necessary for tabulation.
is
   -- A CVR file.
   type Cvr_File is
      record
         The_File: File_Type;
         Some_Cvrs: Ballots;
      end record;

   -- A file that contains a description of a single contest.
   type Contest_File (Max_Choices: Positive) is
      record
         The_File: File_Type;
         A_Contest: Contest;
      end record;

   -- A file describing a simple plurality contest result.
   type Simple_Plurality_Contest_Result_File is
      record
         The_File: File_Type;
         A_Contest_Result: Simple_Plurality_Contest_Result;
      end record;
   
   -- A file describing a multiseat plurality contest result.
   type Multiseat_Plurality_Contest_Result_File is
      record
         The_File: File_Type;
         A_Contest_Result: Multiseat_Plurality_Contest_Result;
      end record;
end Tabulation_IO;
