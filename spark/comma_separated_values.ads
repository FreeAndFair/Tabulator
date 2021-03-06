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
with Tabulation_Constants; use Tabulation_Constants;

package Comma_Separated_Values
-- Encoding of election data using CSVs.
is
   -- Comma separated values (CSVs).
   -- @review kiniry - Make these kinds of types private. Expose exactly
   -- those types mentioned in the BON specification.
   subtype Csv_Value is String(1 .. Max_Csv_Length);
   -- A single list of comma-separated values.
   type Csv is array(Positive range 1 .. Max_Choices) of Csv_Value;
   -- A list of CSVs.
   type Csvs is array(Positive range 1 .. Max_Contests) of Csv;

   -- A CSV file.
   type Csv_File is
      record
         The_File: File_Type;
         Some_Csvs: Csvs;
      end record;

   -- What is your character separator?
   function Separator (A_Csv: in Csv) return Character;
   -- What is the parse of the following string using this character separator?
   function Parse (A_String: in String; A_Character: in Character)
                   return Csv;
   -- What is your ith component?
   -- @design kiniry - Realized by SPARK's array component reference
   -- operator ().
   function Ith (A_Csv: in Csv; An_Index: in Positive)
                 return String;
   -- How many components do you contain?
   -- @design kiniry - Realized by SPARK's array attribute Length.
   function Count (A_Csv: in Csv) return Natural;
   -- invariant
   -- Component indices start with one (1).
   -- @design kiniry - Satisfied by the use of Positive type in all
   -- range declarations.
end Comma_Separated_Values;
