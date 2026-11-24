import YM.Patria.Calm
import YM.TIPS.Fall
/-!
 # Calibrating off coarse carrier. Keep literal paths; no averaging/root translations of unaligned placements without consensus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Depth.Off
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
open Poised Plans Display Orientation Exposure Rolls Canvas
variable {S:Scheme}{r:Side}{N J d i m k:ℕ}(A:Run S N r 6)(H:SourceRead.TaperHol)(sym:RawSym) (B:Bore d)
variable (hf:Rubric sym B) (hA:A.Actual)(W:Market S r d)(hW:Wager A H B W m)
open Planned.PrimaryIntegral295 Carrier
/- path on cover respects EVERY ancestor exactly. -/
def Borders (S:Scheme)(t M:ℕ)(b:ℕ→ Cover):Prop:=∀ i:ℕ,t ≤ i→i < M → cellar (S.step i).L (b (i+1))=b i
variable (b:ℕ→ Cover)(hB:Borders S m N b)
lemma basic : Borders S m N (fun _=>0):=fun _ _ _=> zero_cellar _
lemma offsetC (L:Side)(x y: Cover):cellar L (x+L.val • y)=cellar L x+y:=by
    have ht:= balance L (x+L.val • y); have hg:wrap L (x+L.val • y)= wrap L x:=by rw[map_add,map_nsmul]; ext j; simp [Per]
    rw [hg] at ht; conv at ht=> lhs; lhs; rw [balance L x]
    apply smul_right_injective Cover L.pos.ne'; dsimp only; rw [smul_add]; rw[add_assoc] at ht; exact add_left_cancel ht.symm
local notation "V₀"=> S.side r N
local notation "Sn"=> A.regulator.density
-- geometry.L
abbrev lup (S:Scheme)(b:ℕ→ Cover)(N i:ℕ)(x:Cover):= b N+ratioTo S N i • (x-b i)
abbrev carrier (i:ℕ)(x: Cover)(y:Label d):Insertion (S.side r i) 6:= AllAt A i (A.regulator.density* B (S.side r N) (lup S b N i x) y)
abbrev child (S:Scheme)(b:ℕ→ Cover)(i:ℕ)(x:Cover):= b (i+1)+(S.step i).L.val • (x-b i)
local notation "Tr"=> carrier A B b
lemma carrier_add (y v:Label d):(Tr i) (b i) (y+v)=Tr i (b i) y+ Tr i (b i) v:=by simp_rw [carrier,map_add,mul_add,map_add]
lemma carrier_action (y:Label d)(v:ℂ):(Tr i) (b i) (v • y)= v • Tr i (b i) y:=by unfold carrier; rw[map_smul,mul_smul_comm,map_smul]
lemma submission (x:Cover)(y:Label d): Tr N x y=Sn* B (S.side r N) x y:=by unfold carrier lup; rw [origin,centreN,one_smul]; congr 2; simp
lemma carrier_roll (h:i < N)(x:Cover)(y:Label d): ⇑(Tr i x y)= A.block i (Tr (i+1) (child S b i x) y):=by unfold carrier child; simp_rw [lup, add_sub_cancel_left,route A _ h, step_factor h, Nat.mul_comm (S.step i).L.val, mul_smul]; -- danger route rew both
include hf
lemma carrier_shift (hi:i≤ N)(x x':Cover)(y:Label d): march x' (Tr i x y)=Tr i (x+x') y:=by
     have hh:lup S b N i (x+x')=lup S b N i x+ratioTo S N i • x':=by unfold lup; rw [add_comm x x', add_sub_assoc,smul_add]; abel
     unfold carrier; rw [hh]; refine journey A _ _ _ hi ?_
     funext V; let a:= ratioTo S N i • x'; exact (map_mul (TorusPCAC.Geometry.crank 1 1 (wrap _ a) (TorusPCAC.Geometry.heat a)) ..).trans (congr_arg₂ HMul.hMul (congr_fun (move_pivot A.regulator a rfl) V) (congr_fun (hf.advances (S.side r N) y (lup S b N i x) a) V))
omit hf
-- avoids seam issues once translated
include hB in
lemma child_home (h:m≤ i)(hi:i < N)(x:Cover): cellar (S.step i).L (child S b i x)= x:=by unfold child; rw[offsetC,hB _ h hi]; abel
include hB hW hA hf
lemma ensures (q:Bool)(v:Label d)(hp: v ≠0)(hv:moored v.val q) (hi:i≤N)(hM:m ≤ i): ∃ y:Label d, y≠0 ∧∀ x, W i x y q (Tr i x v):=by
     induction hi using Nat.decreasingInduction with
     | self=> refine ⟨v,hp,fun x=>?_⟩; rw [submission]; have hS:= hW.journey.boot x v q hv hp; rw [hA.start] at hS; exact hS
     | of_succ i hi ih=>
        obtain ⟨y,hp',hy⟩:= ih (hM.trans (Nat.le_succ i)); let U (x:Cover):= child S b i x; let R:= (stitch S r i).ratio
        have hu(x:Cover):R.parent (wrap _ (U x))= wrap _ x:=by rw [Streets.owner,show cellar R.count (U x)=x from child_home _ hB hM hi x]
        choose p ht hg using fun x:Cover=> hW.journey.rolling x i hM hi (Fin 1) (fun _=>1) (fun _=> Tr (i+1) (U x) v) (fun _=> U x) y q hp' (fun _=> zero_le_one) (by simp) (fun j=>⟨by change separation (R.parent _) _ ≤ _; rw[hu]; simp, by change Laurent.size (cellar R.count (U _) - _) ≤ _; rw[show cellar R.count (U x)=x from child_home _ hB hM hi x, sub_self]; simp [Laurent.size]⟩) (fun _=>hy _)
        have hY(x:Cover): W i x (p x) q (Tr i x v):=by rw[carrier_roll A _ _ hi]; simpa only [Complex.ofReal_one,one_smul,Fin.sum_univ_one] using hg x
        let z:= b i; refine ⟨p z,ht z,fun x=>?_⟩
        have hh:= Canvas.moved H (Tr i z v) (x-z) z (hW.journey.furnished z _ _ _ hM hi.le _ (hY z)) (by rw[pier A hA hi.le]; exact first A _ hi.le _)
        rw[carrier_shift A sym B hf b hi.le,add_sub_cancel] at hh; rw [Canvas.consensus _ _ _ hh _ (hW.journey.furnished x _ _ _ hM hi.le _ (hY x))]; exact hY _
end YM.Massive.Patria.Depth.Off
#print axioms YM.Massive.Patria.Depth.Off.submission
#print axioms YM.Massive.Patria.Depth.Off.ensures
