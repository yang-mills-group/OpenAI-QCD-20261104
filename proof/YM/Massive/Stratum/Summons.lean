import YM.Massive.Stratum.Oolitic
import YM.QCD.Disc.Basin
/-!
# The gauge slope and collar capability registered before all strides

The amount needed for the loop fiber alone can be post-stride, with contraction
applied at a return toward coarser plates. Branches must still be checked; no per-flight
ability assumed (especially dependence on train).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D u v x y W:ℝ}{p:ChartRatio su}{B T: Bed}{F L:Side→ℝ}

variable {S:Flight j j} {Λ Γ θ φ φ':ℝ}
structure Summit (S:Flight j j)(K:KernelChoices)(m:SparkMesh)(R' R:PathData su)(q:Clip)(u v:ℝ)(T:Towers S.L)(p:ChartRatio su)(α γ b ψ D:ℝ) where
   place : Place S K m R q u v
   toll : |α+su.slopeConstant*Real.log S.L.val|+1≤D
   gaps i: PriceGap (place.forest i) q R γ
   foresee i : Guessed (place.forest i) (installed (act S K m i).ratio T.A0) (place.u i)
   turns i: ClassicalMatch (place.forest i) q q R R' (place.u i)
   holds i: FiniteBound (place.forest i) R R' q q α p (place.u i) b ψ 1

def Enjoy (M:Bed)(q:Clip)(u v Λ:ℝ)(R:PathData su):Prop := R.Bounds q u v Λ ∧ Attached M R


/-- Single restoring step, costs `F L` and `θ` common to all mesh
sizes, choices of bed roll, AND all flights using the stride. Influence of
gauge paths on spin jets persists in these new steps. -/
lemma uncover (h: PreCut K q j η σ Ω u v γ D n F L)(hL:LocalRatio p)(hη:0<η)(A:Side):
 ∃ c:ℝ,0<c∧∀ (S:Flight j j),S.L=A→ n≤S.L.val→ S.patch.Branches K su →∀ (B T:Bed)(U:Towers S.L)(m:SparkMesh)(R:PathData su)(Λ Λ' Θ:ℝ), QuarryQ q σ η Ω B → QuarryQ q σ η Ω T → DeltaQ K q σ Ω S B T U → 1≤Λ → Λ/2≤Λ'→ L S.L≤Λ' → reachM S.patch m→ F S.L≤Θ→ Enjoy B q u v Λ R →∃ (α:ℝ)(R':PathData su), Enjoy T q u v Λ' R' ∧ Nonempty (Summit S K m R' R q u v U p α c Θ γ D) :=by
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
   have hy' n: Hull T η σ Ω q n su:= ⟨hT.fund.2.1,hT.fund.2.2.2.1,hT.trace,fun _=> hT.oath _⟩
   have hd:Scud X su q q R f V σ u Ω v Ω η Λ σ Ω η B T U P:= ⟨hl,hy _,hy' _,hM,hR,fun l H'=> ((hU.pay.2.2.2 l (H'.trans (by have hj:= S.legal; omega))).1),fun i=>hU.crosses (divides0 S m i),fun i=> (hw i).1,hV,hu,hv⟩
   obtain ⟨R',α,h₁,h₂,h₃,h₄,h₅,h₆⟩:= h m.n _ S.patch X q q _ f V _ _ U Λ η P p rfl hz m.cofinal le_rfl le_rfl hd hΛ hP hL
   refine ⟨α,R',⟨h₃ u v Λ' hR.width le_rfl le_rfl hx hr,h₂⟩,⟨Q,h₄,fun i=>(hw i).1,hu,h₅,h₆ Θ γ hΘ le_rfl⟩⟩

namespace Summit
variable {ν:ℝ}
variable {M:SparkMesh} {R R':PathData su} {U:Towers S.L}
def back (X:Summit S K M R' R q u v U p ν x y γ D) : Back S.patch K j j q u v:=⟨R,S,rfl,M,X.place⟩ -- bind
def avenue (X:Summit S K M R' R q u v U p ν x y γ D)(h:QuarryQ q σ η Ω B)(h':QuarryQ q σ η Ω T)(hp:DeltaQ K q σ Ω S B T U)(hη:0<η):Avenue X.back σ Ω Ω where
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
 paidUp t:=⟨by have e:=S.legal; omega,h.fund.2.2.2.2,h'.fund.1,hp.pay, by intro a b c d; rw [hp.cell]; exact harmonic_column S _ K.penalty_pos S.legal a b c d,h.oath _,⟨_,_,hη,h.trace _⟩,hp.crosses (divides0 S M t), ((X.place).admiss t).1⟩
 merits:=h'.fund.2.1
 home:=(h'.trace 1).starts
 Sw:=fun _=> h'.oath _
end Summit
open ConnectedActivityE6 Pressure Pressure.Stores
structure Bedrock (K:KernelChoices)(Z:Teller su)(V:Train j→ Bed)(D γ v η:ℝ)(n:ℕ)(F L:Side→ℝ): Prop where
 kernel : Z.bind=K
 width : 0<Z.top.width
 orderEq : Z.j=j
 fixedP : Z.top=Z.below
 budget : Z.top.supportExponent=2
 bound : 1 ≤ Z.C
 flour : 0 < η
 cap_norm : 0 ≤ v
 cap : v ≤ Z.top.paths
 clip : Z.top.clip.direct ≤1
 ramp : 0 ≤ D
 clearR : 0<γ
 tally : PreCut K Z.top.clip j η Z.η Z.C Z.top.width v γ D n F L
 roots : ∀ s : ℝ, 0 ≤ s → (Design.top su Z.top.clip).Bounds Z.top.clip Z.top.width v s
 field : Mantle K Z.top.clip Z.η η Z.C n V

lemma climate (K:KernelChoices)(j:ℕ)(hj:4≤j): ∃ (Z:Teller su)(V:Train j→ Bed)(D γ v η:ℝ)(n:ℕ)(F L:Side→ℝ), Bedrock K Z V D γ v η n F L:=by
  obtain ⟨p,hp,s,e,c,hs,hc,hc',n,X,h⟩:= mantel K j hj
  obtain ⟨u,v,d,ψ,hU,hV,hd,hY,h',N,A,Y,ht⟩:=sprouts K p j hp hs hc hc'
  let f:=inflateP p u hU
  obtain ⟨B,hB,hE,h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩:= phonon u v s d f hU hs hV (show 12 ≤12/u*u from by rw [div_mul_cancel₀ _ hU.ne']) hd K j c
  have HH:= cloak u hU h
  refine ⟨B,X,d,ψ,v,e,max n N,A,Y, hB,?_,h₇,h₃.symm,hE,?_,hc,hV,?_,?_,hd,hY,?_,?_,?_⟩
  · rw [h₁]; exact hU
  · rw [h₅]; exact hc'
  · rw [h₂]; linarith
  · rw [h₄]; exact hp
  · rw [h₆,h₄,h₅,h₁]; have he := saluteP p u hU ht
    -- Transition increase delay
    intro m n' P M p' q' R F g V T U Λ ε η L hJ ht'; exact he m n' P M p' q' R F g V T U Λ ε η L hJ ((le_max_right ..).trans ht')
  · intro t hT; rw [h₁,h₄]; exact pathsP p u hU (h' _ hT)
  rw [h₄,h₆,h₅]; exact ⟨HH.fare,HH.top,fun i h=>HH.edges _ ((le_max_left ..).trans h),fun i h=> HH.begins _ ((le_max_left ..).trans h)⟩
end YM.QCD.Acre.Stratum
#print axioms YM.QCD.Acre.Stratum.uncover
#print axioms YM.QCD.Acre.Stratum.climate
#print axioms YM.QCD.Acre.Stratum.Summit.avenue
