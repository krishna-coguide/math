import Erdos272.ScoreTables

namespace E272

theorem score_good {a : Mask} (hs : short a = true) (ha : ap a = true) : score a = 0 :=
  tab_score_good hs ha

theorem score_bad {a : Mask} (hs : short a = true) (ha : ap a = false) : 0 < score a :=
  tab_score_bad hs ha

end E272
