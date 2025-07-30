module PIDMap = Map.Make(Int)

module PidPair = struct
  type t = int * int
  let compare = compare
end

module PIDPIDMap = Map.Make(PidPair)
