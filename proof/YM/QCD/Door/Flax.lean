import YM.QCD.Door.Tails
/-! # wipe weight. Hinge operators lists. -/
set_option maxHeartbeats 40000
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Grass Creek Ledge Function NormedSpace Finset Lat Kit
open scoped Topology BigOperators Classical Matrix Matrix.Norms.L2Operator
variable {A B C D:Type*}[Fintype A][Fintype B][DecidableEq A][DecidableEq B]

lemma pondD (U:Matrix A A ℂ) (V: Matrix B B ℂ)(K:Matrix A A ℂ)(x:Dirac (A⊕B)): disguise (whole U V) (excess (pond (head A B) (U*K*star U)) x)= excess (pond (head A B) K) (disguise (whole U V) x):=lift_p (disguise (whole U V)).toRingHom (disguise (whole U V)).toLinearMap.continuous_of_finiteDimensional _ _ (gust U V K) x
lemma pondY (K:Matrix A A ℂ)(x:Dirac (A⊕B)): surf _ (excess (pond (head A B) K) x)=excess (pond (head A B) (star K)) (surf _ x):=lift_p (rib (A⊕B)) (surf_cont (A⊕B)) _ _ (current K) x

lemma sourceH (S:Matrix A B ℂ)(T:Matrix B A ℂ)(x:Dirac (A⊕B)): excess (bark (bladesF S T)) x = shear S T x-x:=by
  have he : birth (bark (bladesF S T)) x=shear S T x:= (show _ from DFunLike.congr_fun (shear_equals S T).symm x)
  exact congr_arg (·-x) he

lemma barkA (U:Matrix A A ℂ)(V:Matrix B B ℂ) (K:Matrix A B ℂ)(Z:Matrix B A ℂ)(h:U∈unitary _)(hv:V∈unitary _) (x:Dirac (A⊕B)): disguise (whole U V) (excess (bark (bladesF (U*K* star V) (V*Z*star U))) x)=excess (bark (bladesF K Z)) (disguise (whole U V) x):=by
  rw [sourceH,sourceH,map_sub,chop U V K Z 0 0 h hv]
lemma barkY (K:Matrix A B ℂ)(Z:Matrix B A ℂ)(x:Dirac (A⊕B)): surf _ (excess (bark (bladesF K Z)) x)=excess (bark (bladesF Zᴴ Kᴴ)) (surf _ x):=by
  rw [sourceH,sourceH,map_sub,chili]

end YM.QCD.Sway
