import YM.Pollen.Tulip
import YM.Pollen.Aven
import YM.Pollen.Bolt
import YM.Pollen.Chonk
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
open scoped Kronecker
open Grass.Ward Massive.PCAC
set_option quotPrecheck false
variable (F:Flavor 6)(Z:ParcelZ (c:=c))
variable (o: Site c) (J':Bool) (x:Axis)(Y:St c)
local notation "d"=> totalR Y x
local notation "R"=>zone 6 o
local notation "Ψ"=>Modes c 6
local notation "M"=>Sour Ψ
local notation "Uκ"=> capsΛ F
noncomputable def steerX (p: Site c)(y:Bool) : Sour (Modes c 6)→L[ℂ] Sour (Modes c 6) := if y then (LinearMap.mulRight ℂ (zone 6 p)).toContinuousLinearMap else (LinearMap.mulLeft ℂ (zone 6 p)).toContinuousLinearMap -- signatures
noncomputable def facesigmaX (V:Grid c):= cream (steerX o J' (capsΛ F (Y V)))
local notation "Πp"=> facesigmaX F o J'
private lemma pointV (Z: ParcelZ (c:=c)) (U:Grid c): steerX o J' (Uκ (Z.val U)) = if o=(if J' then Z.β else Z.α) then capsΛ F (Z.val U) else 0:=by
    ext i j; have he : capsΛ F (Z.val U) i j= (if i.1.1=Z.α∧ j.1.1=Z.β then Z.f U i.1.2 j.1.2 else 0)*Massive.PCAC.spot F F i.2 j.2:=rfl; let A:Matrix Ψ Ψ ℂ:=capsΛ F (Z.val U); have hg : A i j≠0→i.1.1=Z.α ∧ j.1.1=Z.β:=by
             intro hx; by_contra hw; apply hx; unfold A; rw [he,if_neg hw,zero_mul]
    cases J'
    · change (zone 6 o * A) i j=(if o=(if (false:Bool) then Z.β else Z.α) then A else 0) i j; rw [zleft,show (if (false:Bool) then Z.β else Z.α)= Z.α from rfl]; by_cases hz:i.1.1=o
      · rw [if_pos hz]; split; rfl; next hp=> exact (show A i j=0 from by_contra fun h=> hp (hz.symm.trans (hg h).1))
      rw[if_neg hz]; split; next hp=> exact (show A i j=0 from by_contra fun h=>hz ((hg h).1|>.trans hp.symm)).symm
      next=> rfl

    · change (A * zone 6 o) i j=(if o=(if (true:Bool) then Z.β else Z.α) then A else 0) i j; rw [zright,show (if (true:Bool) then Z.β else Z.α)= Z.β from rfl]; by_cases hz:j.1.1=o
      · rw [if_pos hz]; split; rfl; next hp=> exact (show A i j=0 from by_contra fun h=> hp (hz.symm.trans (hg h).2))
      rw[if_neg hz]; split; next hp=> exact (show A i j=0 from by_contra fun h=>hz ((hg h).2|>.trans hp.symm)).symm
      next=> rfl

open MassiveQCD.Sample.Basal MassiveQCD.Sample.Basal.WindowU
variable {T K:ℝ}
variable (h: Deposits Y p σ T K)(ht:0 < a)
include h ht
local notation "G"=>fingers 6^2*a^2
lemma affordY : Given o p a σ (G*K) (G*T) (Πp Y):=by
     obtain ⟨I,hI,Z,H,rfl⟩:=h.art; obtain ⟨f,g,b,hb,hf,hg⟩:=H.book
     let k:=(Finset.univ:Finset I).filter fun i=> o=(if J' then (Z i).β else (Z i).α); let X:=↥k; let p'(i:X):= (Z i.val).R; have hz(i:X):o∈p' i:=by rw [show o=(if J' then _ else _) from (mem_filter.mp i.2).2]; split; exact (hb _).son; exact (hb _).site -- dependent motive check
     let w'(i:X):= bouquet F ∘ (Z i.val).val; have hQ:0 ≤ G:=mul_nonneg (sq_nonneg _) (sq_nonneg _); have hm (C:I→ℝ)(U:ℝ)(h:Ac.Hit (fun i=>(Z i).R) p.B C σ U): Ac.Hit p' p.B (fun i=> G*C i.val) σ (G*U):=by
             intro i; convert budget_scale hQ (budget_pull (fun j:X=>j.val) Subtype.val_injective (h i)) using 1; funext j; split; next hp=> exact mul_assoc ..
             next=> exact (mul_zero _).symm
     refine ⟨X,inferInstance,p',w',_,_,?_,fun i=> sunup F _ (hb _), hz,fun i=>textile F _ (hb _) ht o (hz i),hm g K hg,hm f T hf,fun i U=> ?_⟩
     · funext U; have hk(q:I): steerX o J' (capsΛ F ((Z q).val U))= if q∈k then capsΛ F ((Z q).val U) else 0:=by rw[pointV]; simp [k] -- edit
       unfold facesigmaX; rw [Finset.sum_apply, map_sum,map_sum,map_sum, Finset.sum_apply]; change ∑ i:I,cream (steerX o J' (capsΛ F ((Z i).val U)))=∑ i:↥k,w' i U; simp_rw [hk]; change _= ∑ i:↥k,bouquet F ((Z i.val).val U); rw [sum_coe_sort k (fun i:I=> bouquet F ((Z i).val U)),←sum_subset (s₁:=k) (subset_univ k) (fun i _ he=> by rw[if_neg he,map_zero])]; exact sum_congr rfl fun i hi=>by rw [if_pos hi]; rfl -- simplify sum indicator.Cone
     let Y':=Z i.val; let z:=Y'.f U; have he: ‖z‖≤ f i:= (le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by simp))).trans ((hb _).global U); exact (milk F _ (hb _) ht z).trans (mul_le_mul_of_nonneg_left he hQ)
omit h ht
-- orientation determinant total. negative sign. AP shift comm.Sensor
noncomputable def aurasigmaMont (V:Grid c) : EvenA c 6:= (-(2:ℂ)⁻¹) • (facesigmaX F o false (totalR Y x) V + facesigmaX F o true (totalR Y x) V)
local notation "W"=> aurasigmaMont
include ht
lemma eraX (hD: Deposits (totalR Y x) p σ T K): Given o p a σ (G*K) (G*T) (W F o x Y):=by
     let z:= -(2:ℂ)⁻¹; let X:=facesigmaX F o false (totalR Y x); let V:=facesigmaX F o true (totalR Y x); have hP := Given.units _ o (Given.plies _ o (affordY F o false (totalR Y x) hD ht) _ (affordY F o true (totalR Y x) hD ht)) z -- order
     convert hP using 1 <;> first | rfl| solve | unfold z; norm_num; ring
omit ht
-- sum. Need sterπ.H.Bean Spin.Low.SupportIncome. no.B
lemma totalSpan (X: Grid c): ∑ p: Site c, facesigmaX F p J' Y X= bouquet F (Y X):=by
     unfold facesigmaX; rw[←map_sum]; apply congr_arg; unfold steerX; split; next h=>
           change (∑ p:Site c,Uκ (Y X)*zone 6 p)=_; rw [← mul_sum, Massive.PCAC.cells,mul_one]; rfl
     change (∑ p:Site c,zone 6 p* Uκ (Y X))=_; rw[← sum_mul,Massive.PCAC.cells,one_mul]; rfl
lemma honing (X:Grid c): ∑ p:Site c,W F p x Y X= -bouquet F (totalR Y x X):=by
      unfold aurasigmaMont; rw [← smul_sum,sum_add_distrib,totalSpan,totalSpan,← two_smul ℂ,smul_smul]; norm_num
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.eraX
#print axioms YM.QCD.Entr.Meridian.honing
