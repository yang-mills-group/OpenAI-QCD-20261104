import YM.Kauri.Step
set_option maxHeartbeats 560000
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open Module
open Ortho (plane Skew)
open Org
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
local notation "Vd"=> K.level 8
abbrev Tarc (K:Choir):Type:= BoxD →ₗ[ℂ] ↥(K.level 8)
noncomputable def tee (f:Tarc K):Hea→ K.W := fun i=> (f (pulseB i)).val
local notation "pB"=> pulseB.toBasis
noncomputable def employ :Tarc K:= pulseB.toBasis.constr ℂ (fun i=> ⟨W i,J.n.tense.lv i⟩)
include J
lemma strongT: tee (employ J)= W:=by funext i; exact congr_arg Subtype.val (pulseB.toBasis.constr_basis _ _ _)
-- mutation representation
noncomputable abbrev L0 (A: Axle K (fun a b=>W (a,b))) (x:Skew): End ℂ (Tarc K):= Mako.power (stall x) (tapeJ K W A le_rfl x)
include H JQ B R
lemma jetG:∃ p:End ℂ (Tarc K), Split p (Set.range (L0 A)):=by
     let L:= yarn J H JQ (d:=8) le_rfl
     let F:Skew →+ End ℂ (Tarc K):= {
          toFun:=L0 A
          map_zero':=by unfold L0; change Mako.power _ (L 0)=_; rw[L.map_zero,show stall 0=0 from ?_]; · apply LinearMap.ext; intro x; apply LinearMap.ext; intro i; rw [Mako.power_app]; simp
                        rw [← zero_smul ℝ (0:Skew),sal]; simp
          map_add':=fun u v=>by unfold L0; rw [cash J H JQ,dome,power_add] }
     let f(u:Skew):= L u; apply surges F
     · intro p q; change clip (Mako.power _ _) (Mako.power _ _)= _; rw [power_bracket, bridge J H JQ B le_rfl R p q,stalk]; rfl
     · intro r p; change Mako.power (stall (r • p)) (tapeJ K W A _ _)=_; rw[sal,gain J H JQ,power_smul]; rfl
     intro i j; exact step (stall (plane i j)) _ (semi _ _ (ally _)) (kinρ J H JQ B le_rfl i j)
-- divergence kernel equation: grade8 f, grade10 output. preserve by induction on FET. symmetric. parity, flux, charge. no orientations.
omit H JQ B R J
structure Pond (u:Tarc K)(T:Pollens P K):Prop where
     sy(a b:Axis): tee u (a,b)= tee u (b,a)
     pa (i:Hea): T.parity (tee u i)= tee u i
     ch(i:Hea): T.charge (tee u i)= tee u i
     fu(f:FlavorTorus)(i:Hea): T.flavor f (tee u i)= tee u i
     di(b:Axis):∑ j:Axis,K.arc j (tee u (j,b))=0
lemma tadd (p q:Tarc K)(i:Hea): tee (p+q) i=tee p i+tee q i:=rfl
lemma tsca (p:Tarc K)(r:ℂ)(i:Hea): tee (r • p) i=r • tee p i:=rfl
lemma tstep (f:Tarc K)(g:Skew)(i j:Axis): tee (L0 A g f) (i,j) = A.jet g (tee f (i,j)) - ((∑ a:Axis,(g.val a i:ℂ) • tee f (a,j))+(∑ b:Axis,(g.val b j:ℂ) • tee f (i,b))):=by
      unfold tee L0; rw [power_app]; simp_rw [Submodule.coe_sub,show pulseB (i,j)=pulseB.toBasis (i,j) from rfl, stave,map_add,map_sum,map_smul,Submodule.coe_add,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul]; rfl
variable {ρ: EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
variable {f:Tarc K}(hh:Pond f T)
include J H JQ B R S hh
lemma d_stance (g:Skew)(b:Axis): (∑ j:Axis,K.arc j (tee (L0 A g f) (j,b)))=0:=by
     let v(i j:Axis):= tee f (i,j); let F(a:Axis)(x:K.W):=K.arc a (A.jet g x)
     have he(i j:Axis): F i (v i j)= A.jet g (K.arc i (v i j))- ∑ a:Axis,(g.val a i:ℂ) • K.arc a (v i j):=by rw [valiant J H JQ B R S]; exact (add_sub_cancel_right ..).symm
     simp_rw[tstep,map_sub,map_add,map_sum,map_smul]; change (∑ i:Axis,(F i (v i b)-((∑ j:Axis,(g.val j i:ℂ) • K.arc i (v j b))+∑ j:Axis,(g.val j b:ℂ) • K.arc i (v i j))))= _; simp_rw [he, Finset.sum_sub_distrib,Finset.sum_add_distrib]; rw [← map_sum,show ∑ i:Axis,K.arc i (v i b)=0 from hh.di b,map_zero]
     rw [show (∑ i:Axis,∑ j:Axis,(g.val j b:ℂ) • K.arc i (v i j))=0 from ?_]; swap; · rw [Finset.sum_comm]; simp_rw [←Finset.smul_sum,show ∀ j,∑ i:Axis, K.arc i (v i j)=0 from fun j=> hh.di j,smul_zero,Finset.sum_const_zero]
     rw [add_zero,zero_sub,sub_eq_zero,Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib,← neg_smul,← Complex.ofReal_neg]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [joy g j i]

lemma wave(g:Skew): Pond (L0 A g f) T:=by
     have h(a: K.W≃ₗ[ℂ]K.W)(he:∀ p,a (tee f p)=tee f p)(hq:∀ v,a (A.jet g v)=A.jet g (a v)) (p:Hea):a (tee (L0 A g f) p)=tee (L0 A g f) p:=by obtain ⟨i,j⟩:=p; rw [tstep]; simp_rw [map_sub,hq,map_add, map_sum,map_smul,he]
     refine ⟨fun a b=>?_,h _ hh.pa (fun v=>halo H _ v H.parity W J.n A g J.n.tense.parity),h _ hh.ch (fun v=>halo H _ v H.charge W J.n A g J.n.tense.charge),fun u=> h _ (hh.fu u) (fun v=>halo H _ v (fun n x hx p=> H.flavor n x hx u p) W J.n A g (fun i=>J.n.tense.flux u i)), d_stance J H JQ B R S hh g⟩
     rw [tstep,tstep,hh.sy a b,add_comm]; apply congr_arg₂ _ rfl; apply congr_arg₂ (· + ·) <;> (apply Finset.sum_congr rfl; intro i _; apply congr_arg; exact hh.sy ..)
end YM.Kauri
#print axioms YM.Kauri.wave
#print axioms YM.Kauri.jetG
