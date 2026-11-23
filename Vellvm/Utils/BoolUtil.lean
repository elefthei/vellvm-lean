module

@[expose] public section
namespace Vellvm.Utils.BoolUtil

def option_pred {A : Type u} (pred : A → Bool) (ma : Option A) := ma.any pred

end Vellvm.Utils.BoolUtil
