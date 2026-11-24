import YM.Mural.Tall
import YM.Play.Lair
/-! An algebraic calculus of a charge array. Additive null rail.
 The extra `none` key for the base column allows row formulas on all arrays without reopening pieces. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.PaletteT
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace
open Plate Stitch Tablet Ribbon
open Lattice Wilson RG
open scoped BigOperators Topology Classical ContDiff
variable {J X P:Type} [Fintype P]
section algebra
variable {A:Type*}[NormedCommRing A][NormedAlgebra ℂ A]
-- π sum over all k. Row sum one. No positivity.
abbrev Frame (P:Type):=Option P
variable (u:(Option P)→ ℂ)(x:(Option P)→A)
noncomputable def aggregate:= ∑ i:(Option P),u i • x i
variable {x}
lemma aggregate_one (hs:∑ i,u i=1) (a:A): aggregate u (fun _=>a)=a:=by unfold aggregate; rw [← Finset.sum_smul,hs,one_smul]
lemma aggregate_mul {x y:(Option P)→ A} (hs : ∑ i,u i=1) (h:∀ i j:(Option P),(x i-x none)*(y j-y none)=0): aggregate u x*aggregate u y=aggregate u (fun i=> x i*y i):=by
   let px i:=x i-x none; let py i:=y i-y none
   let x0:=x none; let y0:=y none
   have h' (W:(Option P)→ A): aggregate u W= W none + aggregate u (fun i=> W i-W none):=by
        unfold aggregate; rw [show ∑ i:(Option P),u i • (_-W none)= _ from Finset.sum_congr rfl (fun i _=> smul_sub (u i) (W i) (W none)), Finset.sum_sub_distrib,← Finset.sum_smul,hs,one_smul]; abel -- binder
   have hp:∀ i, x i*y i-x0*y0=x0*py i+px i*y0 :=by
        intro i
        have he:x i= x0+px i:=by unfold px x0; abel
        have hf:y i = y0+py i:=by unfold py y0; abel
        rw [he,hf,add_mul,mul_add,mul_add,h i i]; abel
   have hz: aggregate u px*aggregate u py=0:=by
       unfold aggregate; rw [Finset.sum_mul]; refine Finset.sum_eq_zero fun i _=>?_ ; rw [Finset.mul_sum]; apply sum_eq_zero; intro j _; rw [smul_mul_assoc,mul_smul_comm,h i j,smul_zero,smul_zero]
   have he : aggregate u x=x0+aggregate u px:=h' x; have hf : aggregate u y=y0+aggregate u py:=h' y
   rw [h' (fun i=>x i*y i),he,hf,add_mul,mul_add,mul_add,hz]
   change _= x0*y0+aggregate u (fun i=>x i*y i-x0*y0); simp only [hp]
   unfold aggregate; rw [Finset.sum_mul,Finset.mul_sum]; simp_rw [smul_mul_assoc, mul_smul_comm,smul_add,sum_add_distrib]; abel
-- at any color, if transformation is linear one step. Staff includes input columns.
end algebra

variable {c:Side} {N:ℕ} {A:Type}[Fintype A]
local notation "T"=> Spine Unit
variable (q:Unit→Bool)
noncomputable abbrev janus:=vacR (Spine Unit) A
structure Loose (x:(Option P)→Patio (A⊕Spine Unit)) : Prop where
 plain: Polite q ∅ (x none)
 finance: ∀ i,ValidPieces A q univ (x i)
 bonds : ∀ i, vacR (Spine Unit) A (x i)= vacR (Spine Unit) A (x none)
-- re-use can mean nonempty for caller.
variable {q} {x y:(Option P)→ Patio (A⊕Spine Unit)}
lemma slateU {x:Patio (A⊕Spine Unit)}(h:ValidPieces A q univ x)(hp:vacR T A x=0) : Polite q {()} x:=by
   apply Polite.of_ranges; intro t ht
   let v:=(pluck A t); change v x=0; rw [← h.wholly, show v (Cupola.chop A q univ x)=_ from control A q _ t x]; split
   next he=>
       obtain ⟨i,hi,hz⟩:=he; have hE:i=∅:=by
          apply Finset.not_nonempty_iff_eq_empty.mp; rintro ⟨y,hj⟩; exact ht (hz.trans (congr_arg _ (Finset.ext fun z' =>by cases z'; cases y; simp [hj]))) -- tags
       rw [hE,burst_absent] at hz; subst t; have hv:=congr_arg Subtype.val hp; change resetM _ _ _=_ at hv; rw [revive] at hv; exact hv
   rfl
lemma ill (h:Loose q x) (i:(Option P)): Polite q {()} (x i - x none):=by
   have hh: ValidPieces A q univ (x i-x none):=by rw [sub_eq_add_neg]; exact (h.finance i).plus (h.finance _).minus
   exact slateU hh (by rw [map_sub,h.bonds]; simp only [sub_self]) -- rewrite issue
lemma fare (h:Loose q x)(hp:Loose q y)(i j:(Option P)): (x i-x none)*(y j-y none)=0:= (ill h i).nilpotent (ill hp j) (by simp)
namespace Loose
lemma light (h:Loose q x)(hp:Loose q y):Loose q (fun i=>x i*y i):=⟨by simpa using h.plain.attached hp.plain,fun i=> (h.finance i).mul (hp.finance i),fun i=>by rw [map_mul,map_mul,h.bonds i,hp.bonds i]⟩
lemma oneV (P A:Type)[Fintype A] [Fintype P] (q:Unit→Bool):Loose (P:=P) q (fun _=> (1:Patio (A⊕Spine Unit))) :=⟨polite_empty_one q,fun _=> ValidPieces.oneV,fun _=>rfl⟩
lemma penny (h:Loose q x)(u:ℂ): Loose q (u • x):= ⟨h.plain.smooch u,fun i=> (h.finance i).tilt u,fun i=>by simp only [Pi.smul_apply,map_smul,h.bonds i]⟩
lemma crest (h:Loose q x)(hp:Loose q y):Loose q (x+y):=⟨h.plain.lays hp.plain,fun i=> (h.finance i).plus (hp.finance i),fun i=>by simp only [Pi.add_apply,map_add,h.bonds i,hp.bonds i]⟩
end Loose
open QCD.Lat MassiveQCD.Cupola
variable (N:ℕ)(p:Unit→Site c)(t:ℝ)
local notation "M"=> ample N Unit
local notation "T'"=> Keys c N⊕Spine Unit
local notation "G"=>EvenA c M
structure Dealers (q:Unit→Bool)(x:(Option P)→EvenA c (ample N Unit)) : Prop where
 act : ∀ i, Well N p t q (x i)
 loose: Loose q (fun i=> withdraw N p t (x i))
noncomputable def graph (q:Unit→Bool) (A:Type)[Fintype A]: Submodule ℂ ((Option P)→Patio (A⊕Spine Unit)) where
 carrier := {x|Loose q x}
 add_mem':= Loose.crest
 smul_mem' c _ h := Loose.penny h c
 zero_mem':= ⟨polite_nil ..,fun i=> ValidPieces.noneV,fun _=>rfl⟩
namespace Dealers
variable {N p t}{x y:(Option P)→ EvenA c (ample N Unit)}
lemma book {w:(Option P)→Patio (Keys c N ⊕ Spine Unit)} (h:Loose q w)(k:0<t): Dealers N p t q (fun i=> banknote N p t (w i)):= by
   have hp i:=h.finance i; refine ⟨fun i=>⟨?_,?_⟩, by simp_rw [home _ _ _ k]; exact h⟩; · unfold Function.comp; rw [home _ _ _ k]
   rw [home _ _ _ k]; exact hp i
lemma suits (hx:Dealers N p t q x) : x= fun i=>banknote N p t (withdraw N p t (x i)):=funext fun i=>(hx.act i).spark.symm
lemma blouse (h:Dealers N p t q x)(hp: Dealers N p t q y)(i j:(Option P)):(x i-x none)*(y j-y none)=0:=by
   rw [suits h, suits hp]; dsimp only; rw [←map_sub (banknote N p t),←map_sub (banknote N p t),← map_mul,fare h.loose hp.loose i j,map_zero] -- rewriting nested x etc
lemma unit (P:Type)[Fintype P] : Dealers (P:=P) N p t q (fun _=>1):=⟨fun _=>Well.oneV,by simp_rw [map_one]; exact Loose.oneV ..⟩
lemma zero (P:Type)[Fintype P] : Dealers (P:=P) N p t q (fun _=>0):=⟨fun _=>Well.zeroV,by simp_rw [map_zero]; exact (graph (P:=P) q (Keys c N)).zero_mem⟩
lemma combine (h:Dealers N p t q x)(hp:Dealers N p t q y): Dealers N p t q (fun i=>x i*y i):=by
    refine ⟨fun i=> (h.act i).boon (hp.act i),?_⟩; simp only [map_mul]; exact Loose.light h.loose hp.loose
noncomputable def clan : Submodule ℂ ((Option P)→ EvenA c (ample N Unit)) where
  carrier:= {x|Dealers N p t q x}
  smul_mem' := by
     intro z x hx; change Dealers N p t q x at hx; refine ⟨fun i=>?_,?_⟩
     · have h:=hx.act i; refine ⟨?_,?_⟩
       · exact (by unfold Function.comp; rw [Pi.smul_apply,map_smul,map_smul]; exact congr_arg (z • ·) h.spark)
       rw [Pi.smul_apply,map_smul]; exact (h.applies.tilt z)
     simp only [Pi.smul_apply,map_smul]; exact Loose.penny hx.loose z
  add_mem' := by
    intro x y h hp; change Dealers N p t q x at h; change Dealers N p t q y at hp; refine ⟨fun i=>?_,?_⟩
    · have hx:=h.act i; have hy:=hp.act i; refine ⟨?_,?_⟩
      · unfold Function.comp; rw [Pi.add_apply,map_add,map_add]; exact congr_arg₂ _ hx.spark hy.spark
      rw [Pi.add_apply,map_add]; exact hx.applies.plus hy.applies
    simp_rw [Pi.add_apply,map_add]; exact Loose.crest h.loose hp.loose
  zero_mem':= Dealers.zero P
end Dealers
end YM.MassiveQCD.PaletteT
#print axioms YM.MassiveQCD.PaletteT.aggregate_mul
#print axioms YM.MassiveQCD.PaletteT.Dealers.clan
#print axioms YM.MassiveQCD.PaletteT.Dealers.blouse
