import YM.QCD.Globe.Ibis
import YM.QCD.Globe.Twirl
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
local notation "V"=> EvenA c N
structure Cocoa (X: V) : Prop where
   flavorG:Fit X
   choco (k:su.El):sways (Lat.rotates N (fun _=>k)) X=X
   cream (t:Strut c)(g p): Warrant t g p → Diode N t p g X=X
   real : Regal c N X=X
lemma Cocoa.add {X Y:V}(h:Cocoa X)(hp:Cocoa Y): Cocoa (X+Y):=by
    exact ⟨fun i he=>(map_add ..).trans (congr_arg₂ _ (h.flavorG i he) (hp.flavorG i he)),fun i=>(map_add ..).trans (congr_arg₂ _ (h.choco i) (hp.choco i)),fun i j k hT=>(map_add ..).trans (congr_arg₂ _ (h.cream i j k hT) (hp.cream i j k hT)), (map_add ..).trans (congr_arg₂ _ h.real hp.real)⟩
lemma Cocoa.sub {X Y:V}(h:Cocoa X)(hp:Cocoa Y): Cocoa (X-Y):=by
    exact ⟨fun i he=>(map_sub ..).trans (congr_arg₂ _ (h.flavorG i he) (hp.flavorG i he)),fun i=>(map_sub ..).trans (congr_arg₂ _ (h.choco i) (hp.choco i)),fun i j k hT=>(map_sub ..).trans (congr_arg₂ _ (h.cream i j k hT) (hp.cream i j k hT)), (map_sub ..).trans (congr_arg₂ _ h.real hp.real)⟩
lemma Cocoa.beat {X:V}(h:Cocoa X)(t:ℝ): Cocoa (wearK c N t X):=by
    exact ⟨fun i he=>(purity ..).trans (congr_arg _ (h.flavorG i he)),fun i=>(purity ..).trans (congr_arg _ (h.choco i)),fun i j k hT=>(purity ..).trans (congr_arg _ (h.cream i j k hT)), (dearR ..).trans (congr_arg _ h.real)⟩
structure Tempo (X:Sheet c):Prop where
    hues (k:su.El): let p:Frame c:=fun _=>k; aura (siteRot p) X=X
    turns (u: Strut c)(g k): Warrant u g k→ aura (haze u k g) X=X
    song: newborn c X=X
lemma Tempo.add {X Y:Sheet c}(hx:Tempo X)(hy:Tempo Y):Tempo (X+Y):=by
   exact ⟨fun k=>(aura_add ..).trans (congr_arg₂ _ (hx.hues k) (hy.hues k)),fun u g k h=>(aura_add ..).trans (congr_arg₂ _ (hx.turns u g k h) (hy.turns u g k h)),(new_add ..).trans (congr_arg₂ _ hx.song hy.song)⟩
lemma Tempo.sub {X Y:Sheet c}(hx:Tempo X)(hy:Tempo Y):Tempo (X-Y):=by
   refine ⟨fun k=>(aura_sub ..).trans (congr_arg₂ _ (hx.hues k) (hy.hues k)),fun u g k h=>(aura_sub ..).trans (congr_arg₂ _ (hx.turns u g k h) (hy.turns u g k h)), ?_⟩
   exact (map_sub (newbornL c) ..).trans (congr_arg₂ _ hx.song hy.song)
lemma Tempo.smul {X:Sheet c}(hx:Tempo X)(a:ℝ):Tempo ((a:ℂ) • X):=by
   refine ⟨fun k=>(aura_scale ..).trans (congr_arg _ (hx.hues k)),fun u g k h=>(aura_scale ..).trans (congr_arg _ (hx.turns u g k h)), ?_⟩; rw [new_smul,hx.song]; simp
lemma Tempo.one : Tempo (1:Sheet c):=by
   refine ⟨fun k=>aura_one (siteRot_u _),fun u g k h=>aura_one (trail h),?_⟩; simp [newborn,aura]
def sunny (P:Plan j)(v: Train j)(c:Side):= wood P (0:Site c) v 1
lemma t_one (t: Strut c) :sky t (1:Grid c)=1:=by ext1 i; simp [Strut.sky,pull,Step.read]
lemma savior (P:Plan j)(v:Train j): Tempo (sunny P v c):=by
    unfold sunny; refine ⟨?_,?_,?_⟩
    · intro k p; let K:= siteRot p; have hh:gauge p (1:Grid c)=1:=by ext1 i; simp [p,Lattice.gauge]
      exact (orbital P 0 v 1 p).symm.trans (congr_arg _ hh)
    · rintro ⟨t,w⟩ g k hp; exact (spin_wood hp.1 hp.2 v P 1).symm.trans (congr_arg _ (t_one (t,w)))
    unfold newborn aura; rw [chi_star,show star (wood _ _ _ _)= _ from spinO P (0:Site c) v 1]; simp only [← Matrix.mul_assoc,chi_sq, Matrix.one_mul]; rw [Matrix.mul_assoc,chi_sq, Matrix.mul_one]
-- Cocoa weight generation
lemma Tempo.butter {X:Sheet c}(hp: Tempo X) (N:ℕ): Cocoa (paleF N X):=by
   have hh(T:Sheet c)(h:T∈unitary _)(ht:aura T X=X): sways (copies N T) (paleF N X)=paleF N X:=by
       have he:aura (star T) X=X:=by nth_rw 1 [← ht]; exact Orbit.compatible T X h
       apply Subtype.ext; change adapter (copies N T) _ (form (copies N X))=form _; rw [form_map,Matrix.transpose_transpose, ← copies_star, ← copies_mul, ← copies_mul]; unfold aura at he; rw [star_star, Matrix.mul_assoc] at he; rw [he] -- assoc direction?
   refine ⟨?_,fun i=>hh _ (siteRot_u _) (hp.hues _),fun i g k h=>hh _ (trail h) (hp.turns i g k h),?_⟩
   · intro i hi; apply Subtype.ext; let A:= flute (Lat.Row c) i; change adapter A _ (form (copies N X))=form _; rw [form_map,Matrix.transpose_transpose]; apply congr_arg; rw [show copies N X*A=A*copies N X from (Sway.column X i).symm, ← Matrix.mul_assoc,(show star A*A=1 from (unit_f hi).1), Matrix.one_mul]
   apply Subtype.ext; let A:= idol c N; change adapter A _ (surf _ (form (Lat.copies N X)))=form _; rw [Port.surf_form,form_map, Matrix.transpose_transpose]; apply congr_arg; unfold A; rw [Sway.starI]; unfold idol; rw [← copies_star,← copies_mul,← copies_mul,← Matrix.mul_assoc]; rw [show chirality c*star X*chirality c=newborn c X by unfold newborn aura; rw [chi_star],hp.song]
lemma Cocoa.pick {X:V}(hp:Cocoa X)(b:Flavor N): Tempo (feeF b X):=by
    have hh(T:Sheet c)(h:T∈unitary _)(hv:sways (copies N T) X=X): aura T (feeF b X)=feeF b X:=by
         have he:=rite X b T hp.flavorG; rw [hv] at he; nth_rw 1 [he]; exact (congr_arg (aura T) (by rw [aura, star_star] : _ = aura (star T) (feeF b X))).trans (inverse_aura _ h)
    refine ⟨fun k=>hh _ (siteRot_u _) (hp.choco _),fun i g k h=> hh _ (trail h) (hp.cream i g k h),?_⟩
    have he:=Stew.burst X b hp.flavorG; rw [hp.real, chi_star] at he; unfold newborn aura; rw [chi_star]; exact he.symm
end YM.QCD.Globe
