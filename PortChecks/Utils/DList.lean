import PortChecks.SourceType
import Vellvm.Utils.DList

universe u

#source_check "src/rocq/Utils/DList.v|Vellvm.Utils.DList|DList_Functor"
  Vellvm.Utils.DList.DList_Functor : Functor Vellvm.Utils.DList.DList.{u}
