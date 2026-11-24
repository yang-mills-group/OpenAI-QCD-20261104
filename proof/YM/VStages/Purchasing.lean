import YM.Massive.Stratum.Summons
import YM.VStages.Linear
/-!
# Teller-edge books pre-L using actual Young columns
 Same output path data at hi-level in all calls. Preparation before real coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D u v x y W:ℝ}{p:ChartRatio su}{B T: Bed}{F L:Side→ℝ}

variable {S:Flight j k} {Λ Γ θ φ φ':ℝ}
variable {q':Clip}
structure Aloft (S:Flight j k)(K:KernelChoices)(m:SparkMesh)(R' R:PathData su)(q q':Clip)(u v:ℝ)(T:Towers S.L)(p:ChartRatio su)(α γ b ψ D:ℝ) where
   place : Place S K m R q u v
   toll : |α+su.slopeConstant*Real.log S.L.val|+1≤D
   gaps i: PriceGap (place.forest i) q R γ
   foresee i : Guessed (place.forest i) (installed (act S K m i).ratio T.A0) (place.u i)
   turns i: ClassicalMatch (place.forest i) q q' R R' (place.u i)
   holds i: FiniteBound (place.forest i) R R' q q' α p (place.u i) b ψ 1

/-- Single restoring step, costs `F L` and `θ` common to all mesh
sizes, choices of bed roll, AND all flights using the stride. Influence of
gauge paths on spin jets persists in these new steps. -/
lemma uncover {u' v':ℝ} (h: Transition su K j η σ Ω q.direct σ Ω q'.direct v u v' D u' γ n F L) (hu':0<u') (hL:LocalRatio p)(hη:0<η)(A:Side):
 ∃ c:ℝ,0<c∧∀ (S:Flight j k),S.L=A→ n≤S.L.val→ S.patch.Branches K su →∀ (B T:Bed)(U:Towers S.L)(m:SparkMesh)(R:PathData su)(Λ Λ' Θ:ℝ), QuarryQ q σ η Ω B → QuarryQ q' σ η Ω T → DeltaW K q q' σ Ω S B T U → 1≤Λ → Λ/2≤Λ'→ L S.L≤Λ' → reachM S.patch m→ F S.L≤Θ→ Enjoy B q u v Λ R →∃ (α:ℝ)(R':PathData su), Enjoy T q' u' v' Λ' R' ∧ Nonempty (Aloft S K m R' R q q' u v U p α c Θ γ D) :=by
   obtain ⟨P,hP,H⟩:= (Integrated.stationary_scene (G:=su) A j K η hη).χ
   refine ⟨P,hP,fun S hs hz hg B T U m R Λ Λ' Θ hB hT hU hΛ hr hx hm hΘ ⟨hR,hM⟩=>?_⟩
   subst A
   let g:= act S K m
   let f i:= Classical.choice (Tree.select (g i).ratio S.odd)
   have hl i: Larger (G:=su) (g i):= reaches hg m hm 0 i
   have hw i:=H _ _ (g i) rfl rfl rfl (hl i) (f i) _ _ _ _ _ _ _ _ _ _ _ U (hU.crosses (divides0 S m i)) (hB.trace _) hR hM (hB.oath _) (hT.trace _)
   choose V hV hu hv using fun j=> (hw j).2
   let Q:Place S K m R q u v:=⟨f,V,hV,hl,Λ,hR⟩
   let X:Armada m.n (high S m) S.patch K:= ⟨fun _=>rfl⟩
   have hy n : Hull B η σ Ω q n su:= ⟨hB.fund.2.1,hB.fund.2.2.2.1,hB.trace,fun _=> hB.oath _⟩
   have hy' n: Hull T η σ Ω q' n su:= ⟨hT.fund.2.1,hT.fund.2.2.2.1,hT.trace,fun _=> hT.oath _⟩
   have hd:Scud X su q q' R f V σ u Ω v Ω η Λ σ Ω η B T U P:= ⟨hl,hy _,hy' _,hM,hR,fun l H'=> ((hU.pay.2.2.2 l (H'.trans (by have hj:= S.legal; omega))).1),fun i=>hU.crosses (divides0 S m i),fun i=> (hw i).1,hV,hu,hv⟩
   obtain ⟨R',α,h₁,h₂,h₃,h₄,h₅,h₆⟩:= h m.n _ S.patch X q q' _ f V _ _ U Λ η P p rfl hz m.cofinal le_rfl le_rfl hd hΛ hP hL
   refine ⟨α,R',⟨h₃ u' v' Λ' hu' le_rfl le_rfl hx hr,h₂⟩,⟨Q,h₄,fun i=>(hw i).1,hu,h₅,h₆ Θ γ hΘ le_rfl⟩⟩

namespace Aloft
variable {ν:ℝ}
variable {M:SparkMesh} {R R':PathData su} {U:Towers S.L}
def back (X:Aloft S K M R' R q q' u v U p ν x y γ D) : Back S.patch K j k q u v:=⟨R,S,rfl,M,X.place⟩ -- bind
def avenue (X:Aloft S K M R' R q q' u v U p ν x y γ D)(h:QuarryQ q σ η Ω B)(h':QuarryQ q' σ η Ω T)(hp:DeltaW K q q' σ Ω S B T U)(hη:0<η)(hk:4≤k): Avenue X.back σ Ω Ω where
 D := B
 D' := T
 T := U
 s:= j-2
 floorP (t):=⟨_,_,h.trace _⟩
 stays t:=hp.crosses (divides0 S M t)
 sworn t:= X.foresee t
 price:= h.fund.2.2.2.2
 nextP:= h'.fund.1
 begun:=by have he:=S.legal; omega
 coins:=hp.pay
 paidUp t:=⟨by have e:=S.legal; omega,h.fund.2.2.2.2,h'.fund.1,hp.pay, by intro a b c d; rw [hp.cell]; exact harmonic_column S _ K.penalty_pos hk a b c d,h.oath _,⟨_,_,hη,h.trace _⟩,hp.crosses (divides0 S M t), ((X.place).admiss t).1⟩
 merits:=h'.fund.2.1
 home:=(h'.trace 1).starts
 Sw:=fun _=> h'.oath _
end Aloft

open ChangeQ
structure Docket (K:KernelChoices) (ns np:ℕ→ℕ) where
   stage (i:ℕ):Stage
   exponent i:(stage i).supportExponent=2
   lattice i:(stage i).order=ns i
   momentum i:(stage i).power=np i
   clip i:(stage i).clip.direct≤1
   beds i: Train (rank i)→Bed
   (width floor cost gamma slope :ChangeQ→ℝ)
   cost_pos b:0<gamma b
   slope_nn b:0 ≤ slope b
   lim : ChangeQ→ℕ
   retail b: Retail K b (fun i=>(stage i).clip) beds (width b) (floor b) (cost b) (lim b)
   crown i:Crown K i (stage i).clip (beds i) (width (steady i)) (floor (steady i)) (cost (steady i)) (lim (steady i))
   (goalsAt postLoop:ChangeQ→Side→ℝ)
   allowance : ℕ → ℝ
   allowance_nn i: 0 ≤ allowance i
   rehearsal (i:ℕ): allowance i ≤ (stage i).paths
   ready (i:ℕ) (Λ:ℝ)(hΛ:0≤Λ): (Design.top su (stage i).clip).Bounds (stage i).clip (stage i).width (allowance i) Λ
   horn b: Transition su K b.old (floor b) (width b) (cost b) (stage b.hi).clip.direct (width b) (cost b) (stage b.lo).clip.direct (allowance b.hi) (stage b.hi).width (allowance b.lo) (slope b) (stage b.lo).width (gamma b) (lim b) (goalsAt b) (postLoop b)

variable (ns np : ℕ → ℕ)
lemma inflateW {V:Towers S.L} (u v:ℝ)(hu:0<u)(hv:0<v)(h: DeltaW K q q' σ Ω S B T V):
    DeltaW K (inflateP q u hu) (inflateP q' v hv) σ Ω S B T V:=
   ⟨h.pay,h.orient,h.cell,h.crosses,fun {c f} hh=> let t:= h.mGauge hh; ⟨t.m,t.n,t.fPart,t.nPart,t.oPart,t.orthogonal⟩⟩

lemma market (K:KernelChoices)(hs:∀ i,6≤ns i)(hp:∀ i,2≤np i): Nonempty (Docket K ns np) := by
   classical
   obtain ⟨p,Y,s,e,C,n,hR,hC,h⟩ := coalition K
   choose v t h₁ h₂ H using fun b:ChangeQ=> transition_cap su lodging simple K b.old (e b) (s b) (C b) (p b.hi).direct (s b) (C b) (p b.lo).direct (hR b).growth (hR b).pos (zero_le_one.trans (hR b).ample) (p _).quadratic_pos.le (hR b).pos (zero_le_one.trans (hR b).ample) (p _).quadratic_pos.le
   let u i:= min (t (steady i)) (t (enter i))
   have hu i:0<u i:= lt_min (h₂ _) (h₂ _)
   choose c hc hc' using fun i=> Design.bound_arbitrary (p i) su (h i) (u i) (hu i)
   let A(i:ℕ):= max (c i) (max (v (steady i)) (v (enter i)))
   have hA i: 0 ≤ A i:= (hc i).le.trans (le_max_left ..)
   choose d ψ Wρ X Yw he hy hz using fun b=> H b (u b.hi) (A b.hi) (hu _) (hA _) (pouring su simple _ _ _ _ _ _ (hR b).pos (hR b).growth (zero_le_one.trans (hR b).ample) (p _).quadratic_pos.le (hu _) (hA _))
   let J i:Stage:= ⟨inflateP (p i) (u i) (hu i),ns i,np i,2,u i,A i + 1,0,1,hs i,hp i,by norm_num,hu i,by have := hA i; positivity,le_of_eq (show 12=12/u i*u i from (div_mul_cancel₀ _ (hu i).ne').symm),le_rfl,le_rfl⟩
   let k(b):= max (n b) (Wρ b)
   refine ⟨J,fun _=>rfl,fun _=>rfl,fun _=>rfl,h, Y, s,e,C,ψ,d,hy,he,k,fun b=> ?_,fun i=> ?_, X,Yw,A,hA,fun i=> le_add_of_nonneg_right zero_le_one,fun i Λ he=> pathsP (p i) (u i) (hu i) (hc' i _ (le_max_left ..) Λ he), fun b=>?_⟩
   · obtain ⟨h,h₁,h₂,h₃,h₄,h₅⟩:= hR b
     refine ⟨h,h₁,h₂, fun i=>QuarryQ.inflate _ (hu _) _ (h₃ i),fun i=>QuarryQ.inflate _ (hu _) _ (h₄ i),fun S ht=>?_⟩
     obtain ⟨V,hV⟩:= h₅ S ((le_max_left ..).trans ht); exact ⟨V,inflateW _ _ (hu _) (hu _) hV⟩
   · obtain ⟨h,hc⟩:= hC i; refine ⟨QuarryQ.inflate _ (hu _) _ h,fun S hS hv=>?_⟩; obtain ⟨V,hV⟩:= hc S ((le_max_left ..).trans hS) hv; exact ⟨V,inflateW _ _ (hu _) (hu _) hV⟩
   have hv:v b ≤ A b.lo:=by obtain ⟨i,j,h⟩:=b; rcases h with h|h; subst j; exact (le_max_left ..).trans (le_max_right ..); subst j; exact (le_max_right ..).trans (le_max_right ..)
   have ht:u b.lo≤t b:=by obtain ⟨i,j,h⟩:=b; rcases h with h|h; subst j; exact min_le_left ..;subst j; exact min_le_right ..
   -- raise n
   exact Transition.preserves (hz b) ht hv le_rfl (le_max_right ..) le_rfl le_rfl le_rfl
end YM.QCD.Acre.Stratum.MarchQ
