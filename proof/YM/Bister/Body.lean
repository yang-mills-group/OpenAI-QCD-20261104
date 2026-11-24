import YM.Bister.Golden
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate.Stretch
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{I X E:Type}{N:ℕ}{σ v k t:ℝ}
variable [Fintype I] (N)(o:I→Site c)(q:I→Bool)
local notation "N'"=> ample N I
variable (X: Patron.Rail c (ample N I) X)(Z:Patron.Rail c (ample N I) E)(i:E→Hat c) {θ A b ρ r m:ℝ}{P:BudgetPoint}
local notation "◎"=> Basin Z i P.threshold
local notation "Ω"=> Ruby.home Z
set_option quotPrecheck false
local notation "V!"=> (vacR (Spine I) (Keys c N)).comp (withdraw N o θ)
variable (h:Vital Z i P.threshold)(ht:∀ j U,Well N o θ q (Z.warp j U))
open Trees
include h ht
lemma supportTip (hz:Quits Z P.B ρ m (A+b) θ)(hτ:1 ≤ m)(ha:0 ≤ A)(hρ:0<ρ)(hb:0<b)(hr:r<1)(hm:degreePrice P.B ρ b≤r)(he:ρ*(1-r)⁻¹ ≤ 1): Wage.Tip N o q ◎ P θ A m:=by
    refine ⟨⟨rank Z i h,dusts Z i h,wealth Z i hτ ha hz hρ hb hr hm he⟩,fun i V0=> ?_⟩; change Well _ _ _ _ (patientY ..); unfold patientY; split; exact Well.product _ _ (fun j _=>ht j _) -- args
    exact Well.zeroV
omit ht
-- canonical preserve: require σ old index injection for exact-single receipts; J alternatives outside σ pay V=0.
variable {D:Type}
local notation "Zp"=> faultK N o θ Z
variable (s : D ↪ E) (Y:Patron.Rail c (ample N I) D)
local notation "FY"=> faultK N o θ Y
variable (hp: ∀ j:D, Z.addr (s j)= i (s j)) (hs:∀ j:D, Z.addr (s j)= Y.addr j)(hu:∀ j:D, Z.warp (s j)=Y.warp j)(hS:∀ j:E, j∉ Set.range s→∀ U,(vacR (Spine I) (Keys c N)).comp (withdraw N o θ) (Z.warp j U)=0) -- force-Old semantics.
-- notation use bug explicit. θ implicit in binder.L.s.
noncomputable def rootE : D ↪ Quants Z i := Function.Embedding.trans s ⟨fun j=> ⟨{j},by
    refine ⟨(?_:separated _ _), Finset.singleton_nonempty _,?_⟩
    · rw [GasP.close]; intro k hk m hm h; exact False.elim (h ((Finset.mem_singleton.mp hk).trans (Finset.mem_singleton.mp hm).symm))
    rintro v hv q hq'; rw [mem_singleton.mp hv,mem_singleton.mp hq']; exact Relation.ReflTransGen.refl⟩, fun a b h=> Finset.singleton_injective (Subtype.ext_iff.mp h)⟩
local notation "Ξ"=> rootE _ Z i s
omit h
lemma owned (x:D) : (◎).addr (Ξ x)=Z.addr (s x):=by
    let p:= (s x); have he (i j:Hat c)(hp:i.place=j.place)(ht:i.inv=j.inv):i=j:=by cases i; cases j; congr
    exact he _ _ (singleton_biUnion ..) (singleton_biUnion ..)
include hs hu
lemma pearls (x:D)(hr:Y.Reg P.threshold): (◎).warp (Ξ x)=Z.warp (s x):=by
    funext U; let y:= s x; change patientY Z {y} P.threshold U=_; unfold patientY booksY coverY; rw [singleton_biUnion,singleton_biUnion]; change (if flags P.threshold U∩ (Z.addr (s x)).place=(Z.addr (s x)).inv then _ else _) = _; rw [prod_singleton,hu,hs]; split; rfl
    next h=>exact Eq.symm (by_contra fun hx=>h (hr.buys x _ hx))
omit hs hu
include hp hS
lemma removes (j:Quants Z i)(hj:j ∉ Set.range (rootE N Z i s)) (U:Grid c) : V! ((Basin Z i P.threshold).warp j U)=0:=by
   by_cases he:∀ x∈j.val,x∈ Set.range s
   · exfalso; obtain ⟨x,hx⟩:= j.2.2.1; obtain ⟨y,hy⟩:= he _ hx; have ht(a b:E)(hK:Ac.bonds Ω j.val a b):a=b:=by
            obtain ⟨ha,hb,w,hF,hK⟩:=hK; obtain ⟨p,rfl⟩:=he _ ha; obtain ⟨q,rfl⟩:=he _ hb; exact by_contra fun h=>Finset.disjoint_left.mp ((GasP.close E _ _|>.1 j.2.1) ha hb h) (show w∈(i (s p)).place from (show (Z.addr _).place=(i (s p)).place from congr_arg Hat.place (hp _)) ▸ (show w∈ (Z.addr (s p)).place from hF)) (show w∈(i (s q)).place from (show (Z.addr _).place=(i (s q)).place from congr_arg Hat.place (hp _)) ▸ (show w∈ (Z.addr (s q)).place from hK))
     have h(a b:E)(h:Ac.chain Ω j.val a b):a=b:=by induction h with | refl=> rfl| tail _ h ih=>exact ih.trans (ht _ _ h)
     apply hj; refine ⟨y,Subtype.ext ?_⟩; change {s y}=j.val; ext a; rw [hy,mem_singleton]; exact ⟨fun h=> h.symm ▸ hx,fun H=>h _ _ (j.2.2.2 _ H _ hx)⟩
   push_neg at he; obtain ⟨k,hk,hq⟩:= he; change V! (patientY ..)=0; unfold patientY; split; · rw [map_prod]; exact prod_eq_zero hk (hS _ hq U)
   exact map_zero _
include hs hu
variable {J:Type}
lemma cring (Y0:Patron.Rail c N J)(hX:Correspond (faultK N o θ Y) Y0)(he:Y.Reg P.threshold)(hw:∀ U,Summable fun j=> ‖(◎).warp j U‖): Correspond (faultK N o θ ◎) Y0:=by
    refine ⟨fun U=>Film.payable (V!).toLinearMap.toContinuousLinearMap (hw U),hX.coins,fun H U=>Eq.trans ?_ (hX.governs H U)⟩; rw [fingerprint,fingerprint]; let f(j:Quants Z i):= if (◎).addr j=H then V! ((◎).warp j U) else 0
    have hf: Function.support f ⊆ Set.range Ξ:=fun j h=> by
           by_contra hu; change f _≠0 at h; unfold f at h; split at h; exact h (removes N o Z i s hp hS j hu U); exact h rfl
    apply Eq.trans (Embedding.injective (Ξ)|>.tsum_eq hf).symm; refine tsum_congr fun j=>?_ ; change f (Ξ j) = ite (Y.addr j=H) _ _; unfold f; rw [owned,pearls N Z i s Y hs hu _ he, hs,hu]; rfl
end YM.MassiveQCD.Plate.Stretch
#print axioms YM.MassiveQCD.Plate.Stretch.cring
