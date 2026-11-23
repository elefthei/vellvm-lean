module

@[expose] public section
namespace Vellvm.Utils.OptionUtil

def from_option {A : Type u} («def» : A) (opt : Option A) := opt.getD «def»

end Vellvm.Utils.OptionUtil
