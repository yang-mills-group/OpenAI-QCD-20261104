import YM.Kauri.Aries
import YM.Kauri.Cairn
set_option autoImplicit false
noncomputable section
namespace YM.Kauri
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open Massive.Patria.Gall Massive.Patria.Gall.Onyx Massive.Tarn.ChargeQ
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder InnerProductSpace
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates Mako
open Module (End)
open Ortho (plane Skew)
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {W:Axis× Axis→ K.W}{A:Axle K (fun a b=>W (a,b))}{φ:ℕ→ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{I:ℕ→ℕ}(J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R:Roof P.sym)
variable {ρ:EuPin→* (K.W≃ₗ[ℂ]K.W)}(S:Steps (A:=A) T R ρ)
variable {p:End ℂ (Tarc K)}(h:Split p (Set.range (L0 A)))
-- stress limit without needing corrected frames
local notation "Ω"=> Free.Symbol 8
include J
noncomputable def suitT (u:Tarc K)(k:ℕ):BoxD →ₗ[ℂ] Free.Symbol 8:=
     ((E.B (I k)).r:ℂ)^4 • ((X.frame (I k) 8).symm.toLinearMap ∘ₗ u)
-- include J? must force binder through function proof, call with named parameters
lemma psalm : ∀ x:BoxD,Tendsto (fun k=>suitT (X:=X) (I:=I) (employ J) k x) atTop (𝓝 (feeF x)):=by
     intro x; have hh(i:Hea): Tendsto (fun k=> suitT (X:=X) (I:=I) (employ J) k (pulseB i)) atTop (𝓝 (feeF (pulseB i))):=by
           rw[ele]; apply (tendsto_pi_nhds.mp J.sea i).congr'
           refine Eventually.of_forall fun v=>?_ ; dsimp only; unfold suitT; rw [LinearMap.smul_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,show employ J (pulseB i)=⟨W i,J.n.tense.lv i⟩ from pulseB.toBasis.constr_basis _ _ _]; rfl
     rw[← pulseB.toBasis.sum_repr x]; simp only [map_sum,map_smul]; exact tendsto_finsetSum _ fun i _=>tendsto_const_nhds.smul (hh i)
lemma pulse_inv (f:Tarc K)(g:Skew)(k:ℕ)(x:BoxD) : suitT (X:=X) (I:=I) (L0 A g f) k x=steel W E X A le_rfl g (I k) (suitT (X:=X) (I:=I) f k x)- suitT (X:=X) (I:=I) f k (stall g x):=by -- use explicit Hd d
     unfold suitT L0 steel; simp [power_app,smul_sub]
include R h
lemma twilight (G:End ℂ (Tarc K)) (hf:Fet (Set.range (L0 A)) G)(f:Tarc K) (L:BoxD→ₗ[ℂ] Free.Symbol 8)(hx : ∀ v:BoxD,Tendsto (fun k=>suitT (X:=X) (I:=I) f k v) atTop (𝓝 (L v)))(hp:L=0∨L=feeF): ∀ v:BoxD,Tendsto (fun k=>suitT (X:=X) (I:=I) (G f) k v) atTop (𝓝 (0:Free.Symbol 8)):=by
     induction hf generalizing f L with
     | mem G hm=>
          obtain ⟨g,rfl⟩:=hm; intro v; simp_rw [pulse_inv J];
          have ht:= ( (follows_L (fun i=>steel W E X A le_rfl g (I i)) (rain g 8) (goes J le_rfl g) _ _ (hx v)).sub (hx (stall g v))); rcases hp with rfl|rfl
          · simpa using ht -- def np???
          rw [themes R g,sub_self] at ht; exact ht
     | zero => intro x; simp [suitT]
     | times a b _ _ ih hv=> exact ih _ 0 (hv f L hx hp) (Or.inl rfl)
     | add a b _ _ ih hv=>
           intro v; have ht:=(ih f L hx hp v).add (hv f L hx hp v); rw [add_zero] at ht; apply ht.congr'; refine Eventually.of_forall fun i=>?_ ; simp only [LinearMap.add_apply, suitT,LinearMap.smul_apply,LinearMap.comp_apply,map_add,smul_add]
     | smul r p _ ih=>
           intro v; have ht:= (tendsto_const_nhds (x:=r)).smul (ih f L hx hp v); rw [smul_zero] at ht; apply ht.congr'; refine Eventually.of_forall fun i=>?_ ; change r • _ =_; simp only[suitT,LinearMap.smul_apply,LinearMap.comp_apply,map_smul]; exact smul_comm ..
lemma projected (v:BoxD): Tendsto (fun i=>suitT (X:=X) (I:=I) (p (employ J)) i v) atTop (𝓝 (feeF v)):=by
      have hh:= twilight J R h (p-1) h.budget _ _ (psalm J) (Or.inr rfl) v; have he:= hh.add (psalm J v); rw [zero_add] at he; apply he.congr'; refine Eventually.of_forall fun i=>?_ ; simp [suitT,smul_sub]
lemma portends:∀ z:ℂ,tee (p (employ J))≠ z • tepid P K:=by
     intro z hz; obtain ⟨a,b,ha,hb⟩:= eyes R; let i:Hea:=(a,b); have he:p (employ J) (pulseB i) = 0:= by apply Subtype.ext; change tee _ i=0; rw[hz]; simp only[Pi.smul_apply,tepid,i,Prod.fst,Prod.snd,if_neg ha,smul_zero]
     apply hb; rw[←ele]; apply tendsto_nhds_unique (projected J R h _); apply tendsto_const_nhds.congr'; refine Eventually.of_forall fun j=>?_ ; dsimp only; unfold suitT; rw [LinearMap.smul_apply,LinearMap.comp_apply, he,map_zero,smul_zero]
-- uplift full W via charter. identity geometry.
omit h
include S H JQ B
lemma cector (t:EuPin)(i j:Axis): ρ t ((tepid P K) (i,j))=∑ a:Axis,∑ b:Axis,(↑(t.coord.val a i*t.coord.val b j):ℂ) • (tepid P K) (a,b):=by
      obtain ⟨F,hF⟩:= loans J H JQ B R 8 le_rfl; let U:= lampU P K; have hp:ρ t U=U:=by rw [← show (F (projection (P.sym.unit 8))).val=U from hF.unit,S.tones _ le_rfl F hF,u_one]
      simp only[tepid,smul_ite,smul_zero,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]; rw [← Finset.sum_smul,← Complex.ofReal_sum,horiz]; split <;> rename_i hi; · simp [show ρ t (lampU P K)=_ from hp, *]; rfl
      simp [*,hp]
variable {e β:ℝ}(hc:C.Path β e)(hP:P.System)(ht:Tendsto φ atTop atTop)
variable (hD:(swingE K 1).range=(bits K).range)(hμ:Module.finrank ℂ (obσ 1 K).range=22)(hV:Module.finrank ℂ (bits K).range=20)(hχ:∀ d,∃ n:Lattice.Side,Injective (P.candidate d n 0))
include hc ht hP hD hμ hV hχ
lemma arp(s:EuPin)(a b:Axis): ρ s (W (a,b))=∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • W (i,j):=by
     obtain ⟨m,hm⟩:=jetG J H JQ B R; let v:= tee (m (employ J)); have hh:= feed J H JQ B R S hm; obtain ⟨F,hF⟩:=loans J H JQ B R 8 le_rfl; let Tt:=fun t a b=> fully J H JQ B R S hm F hF t a b
     have he : Tense T v∧ divR K v=0:=by
            refine ⟨⟨fun i=>(m (employ J) _).property,hh.sy,hh.pa,hh.ch,hh.fu,fun i t hi x y=>?_⟩,?_⟩ -- names
            · rw [← S.acts JQ.h (loans J H JQ B R) _ _ hi]; exact (Tt i x y).trans (Massive.Tarn.ChargeQ.EuM_w T v ρ (fun t s h=> S.acts JQ.h (loans J H JQ B R) t s h) x y i t hi)
            funext i; change divR K v i=0; unfold divR; rw [LinearMap.pi_apply,LinearMap.sum_apply]; exact hh.di i
     obtain ⟨x,y,HQ⟩:= (chartered hc hP ht T H JQ hD hμ hV hχ W v J.n).mp he; have hp:x≠0:=by intro e; rw [e,zero_smul,zero_add] at HQ; exact portends J R hm y HQ
     have hu:v (a,b)=v (a,b):=rfl; have hv:ρ s (v (a,b))= ∑ i:Axis,∑ j:Axis,(↑(s.coord.val i a*s.coord.val j b):ℂ) • v (i,j):= Tt ..; apply (smul_right_injective _ hp); rw [HQ] at hv
     simp_rw [Pi.add_apply, Pi.smul_apply, map_add, map_smul, smul_add,Finset.sum_add_distrib] at hv
     rw [cector J H JQ B R S] at hv; let V(i j:Axis):ℂ:= ↑(s.coord.val i a*s.coord.val j b); have h(q:ℂ)(F:Hea→ K.W): q • (∑ i:Axis,∑ j:Axis, V i j • F (i,j))=∑ i:Axis,∑ j:Axis,V i j • q • F (i,j):=by simp_rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; exact smul_comm ..
     change x • ρ s _ + y • (∑ i,∑ j,V i j • _)=_ at hv
     rw [h y (tepid P K),←h x W] at hv; exact add_right_cancel hv
end YM.Kauri
#print axioms YM.Kauri.projected
#print axioms YM.Kauri.arp
