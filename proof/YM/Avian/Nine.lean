import YM.Avian.Recan
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Seals
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open StressFlux (pairDeriv curl0 curl1 leg0 leg1)
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
local notation "Q★"=> (0:Multi 8)
local notation "Y"=>UV.first
local notation "Z"=>(0:Multi 10)
local notation "B"=> leadR
local notation "X"=> ηR
local notation "I₁"=> (0:Axis)
local notation "J₁"=> (1:Axis)
variable (a b:Flavor 6) (x y:ℂ)(u:Values 4)(z:Fin 4→ℂ)(v:Values 2)(i j:Axis)
local notation "Sz"=> RawTensor
local notation "HP"=>RawVec 10
local notation "θσ"=>RawTensor 1 8
local notation "θα"=>RawTensor (-1) 8
abbrev FacesT:= Flavor 6→ Fin 6→ Spike
noncomputable def qv (a:Flavor 6)(p q:Multi 10): HP→ₗ[ℂ]Spike:= prism0 a p q ∘ₗ (UV.labels 10).subtype ∘ₗ LinearMap.proj 0 ∘ₗ (RawVec 10).subtype
noncomputable def ts (x:ℂ)(a: Flavor 6)(p q:Multi 8)(i:Axis): Sz x 8 →ₗ[ℂ] Spike:= prism0 a p q ∘ₗ (UV.labels 8).subtype ∘ₗ LinearMap.proj (i,I₁) ∘ₗ (RawTensor x 8).subtype
noncomputable def obV : HP →ₗ[ℂ] FacesT := LinearMap.pi fun a=> LinearMap.pi (![qv a Z (B I₁), qv a Z (B J₁), qv a Z (X I₁ I₁), qv a Z (X J₁ J₁), qv a Z (X I₁ J₁), qv a (B J₁) (B I₁)])
noncomputable def obS (x:ℂ) : RawTensor x 8→ₗ[ℂ] FacesT:= LinearMap.pi fun a=> LinearMap.pi (![ts x a Q★ Q★ I₁,ts x a Q★ Q★ J₁,ts x a Q★ (Y I₁) I₁,ts x a Q★ (Y J₁) J₁,ts x a Q★ (Y J₁) I₁+ts x a Q★ (Y I₁) J₁,ts x a Q★ (Y I₁) J₁+ts x a (Y J₁) Q★ I₁])
local notation "Q" => qv a
local notation "T"=> ts x a
variable (p:Multi 10)(q:Multi 8)(L: RawTensor x 8)(H:RawVec 10)
lemma ob_sn0: obS x L a 0=ts x a Q★ Q★ I₁ L:=rfl
lemma ob_ve0: obV H a 0=qv a Z (B I₁) H:=rfl
lemma ob_sn1: obS x L a 1=ts x a Q★ Q★ J₁ L:=rfl
lemma ob_ve1: obV H a 1=qv a Z (B J₁) H:=rfl
lemma ob_sn2: obS x L a 2=ts x a Q★ (Y I₁) I₁ L:=rfl
lemma ob_ve2: obV H a 2=qv a Z (X I₁ I₁) H:=rfl
lemma ob_sn3: obS x L a 3=ts x a Q★ (Y J₁) J₁ L:=rfl
lemma ob_ve3: obV H a 3=qv a Z (X J₁ J₁) H:=rfl
lemma ob_sn4: obS x L a 4=ts x a Q★ (Y J₁) I₁ L+ts x a Q★ (Y I₁) J₁ L:=rfl
lemma ob_ve4: obV H a 4=qv a Z (X I₁ J₁) H:=rfl
lemma ob_sn5: obS x L a 5=ts x a Q★ (Y I₁) J₁ L+ts x a (Y J₁) Q★ I₁ L:=rfl
lemma ob_ve5: obV H a 5=qv a (B J₁) (B I₁) H:=rfl
lemma life_v (M:Values 7) (t:Fin 3→ℂ):
    let z:=obV (plaza (M,t)) a; let x:=M a
    z 0= x 0 • (1:Spike) + x 1 • (1:Spike) ∧
    z 1=x 1 • (gamma I₁ * gamma J₁) ∧ z 2=x 2 • gamma I₁+x 3 • gamma I₁+x 4 • gamma I₁ ∧ z 3=x 3 • gamma I₁ ∧ z 4=x 4 • gamma J₁ ∧ z 5=x 5 • gamma J₁:=by
    intro z x; exact ⟨(coast a M t I₁ Z (B I₁)).trans (row0 a _), (coast a M t I₁ Z (B J₁)).trans (row1 a _), (coast a M t I₁ Z (X I₁ I₁)).trans (row2 a _), (coast a M t I₁ Z (X J₁ J₁)).trans (row3 a _), (coast a M t I₁ Z (X I₁ J₁)).trans (row4 a _), (coast a M t I₁ (B J₁) (B I₁)).trans (row5 a _)⟩
lemma ts_value(a: Flavor 6)(x:ℂ)(p q: Multi 8)(i:Axis)(G:RawTensor x 8) : ts x a p q i G = prism0 a p q ((G.val (i,I₁)).val):=rfl
lemma life_c : let M:= poseσ (u,z); let p:= u a; let F:= obS 1 M a; let G:=poseα v; let H:=obS (-1) G a; let q:= v a
    F 0=p 0 • (1:Spike)∧ H 0=0 ∧ F 1=0 ∧ H 1=0 ∧ F 2= (p 1 * 2 + p 2 * 2 + p 3) • gamma I₁ ∧ H 2=0 ∧ F 3=p 1 • gamma I₁ ∧ H 3= -(q 0 • gamma I₁) ∧ F 4= (p 1+p 3) • gamma J₁ ∧ H 4=q 0 • gamma J₁ ∧ F 5=(p 1-p 3) • gamma J₁ ∧ H 5=q 0 • gamma J₁:=by
    intro M p F G H q; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold F
      rw [ob_sn0,ts_value a 1 Q★ Q★ I₁]; unfold M; rw [sLead0]
      all_goals unfold p; module
    · unfold H
      rw [ob_sn0,ts_value a (-1) Q★ Q★ I₁]; unfold G; rw [aLead0]
      all_goals unfold q; module
    · unfold F
      rw [ob_sn1,ts_value a 1 Q★ Q★ J₁]; unfold M; rw [sLead1]
      all_goals unfold p; module
    · unfold H
      rw [ob_sn1,ts_value a (-1) Q★ Q★ J₁]; unfold G; rw [aLead1]
      all_goals unfold q; module
    · unfold F
      rw [ob_sn2,ts_value a 1 Q★ (Y I₁) I₁]; unfold M; rw [sLead2]
      all_goals unfold p; module
    · unfold H
      rw [ob_sn2,ts_value a (-1) Q★ (Y I₁) I₁]; unfold G; rw [aLead2]
      all_goals unfold q; module
    · unfold F
      rw [ob_sn3,ts_value a 1 Q★ (Y J₁) J₁]; unfold M; rw [sLead3]
      all_goals unfold p; module
    · unfold H
      rw [ob_sn3,ts_value a (-1) Q★ (Y J₁) J₁]; unfold G; rw [aLead3]
      all_goals unfold q; module
    · unfold F
      rw [ob_sn4,ts_value a 1 Q★ (Y J₁) I₁,ts_value a 1 Q★ (Y I₁) J₁]; unfold M; rw [sLead4,sLead5]
      all_goals unfold p; module
    · unfold H
      rw [ob_sn4,ts_value a (-1) Q★ (Y J₁) I₁,ts_value a (-1) Q★ (Y I₁) J₁]; unfold G; rw [aLead4,aLead5]
      all_goals unfold q; module
    · unfold F
      rw [ob_sn5,ts_value a 1 Q★ (Y I₁) J₁,ts_value a 1 (Y J₁) Q★ I₁]; unfold M; rw [sLead5,sLead6]
      all_goals unfold p; module
    · unfold H
      rw [ob_sn5,ts_value a (-1) Q★ (Y I₁) J₁,ts_value a (-1) (Y J₁) Q★ I₁]; unfold G; rw [aLead5,aLead6]
      all_goals unfold q; module
lemma skipσ (h:obS 1 (poseσ (u,z))+obS (-1) (poseα v)=0) : u=0∧∀ a:Flavor 6,v a 0=0:=by
    have hP (a:Flavor 6):u a=0∧v a 0=0:=by
           let p:=u a; let q:=v a; let F:= obS 1 (poseσ (u,z)) a; let H:= obS (-1) (poseα v) a; have ht(i:Fin 6):F i+H i=0:=congr_fun (congr_fun h a) i
           obtain ⟨h0,j0,h1,j1,h2,j2,h3,j3,h4,j4,h5,j5⟩:= life_c a u z v
           have he: p 0=0:=by apply probe_one; rw [← h0]; exact (add_zero _).symm.trans ((show F 0+0=0 from j0 ▸ ht 0)) -- rewrite test
           have he2 : p 1*2+p 2*2+p 3=0:=by
                apply probe_zero I₁; rw [← ht (2:Fin 6)]
                rw[show F 2=_ from h2,show H 2=_ from j2]; unfold p; module
           have he3 : p 1-q 0=0:=by
                apply probe_zero I₁; rw [← ht (3:Fin 6)]
                rw[show F 3=_ from h3,show H 3=_ from j3]; unfold p q; module
           have he4 : p 1+p 3+q 0=0:=by
                apply probe_zero J₁; rw [← ht (4:Fin 6)]
                rw[show F 4=_ from h4,show H 4=_ from j4]; unfold p q; module
           have he5 : p 1-p 3+q 0=0:=by
                apply probe_zero J₁; rw [← ht (5:Fin 6)]
                rw[show F 5=_ from h5,show H 5=_ from j5]; unfold p q; module
           have hp: p 1=0 ∧ p 2=0 ∧ p 3=0 ∧ q 0=0:=by
               have ht: p 3=0:=by linear_combination (he4-he5)/2
               have hy: p 1=0:=by linear_combination (he4-ht+he3)/2
               refine ⟨hy,?_,ht,?_⟩
               · linear_combination (he2-ht-2*hy)/2
               linear_combination hy-he3
           refine ⟨funext fun i=> ?_,hp.2.2.2⟩; fin_cases i; exact he; exact hp.1; exact hp.2.1; exact hp.2.2.1
    exact ⟨funext fun i=>(hP i).1,fun a=>(hP a).2⟩
end YM.Massive.Patria.Gall.Seals
#print axioms YM.Massive.Patria.Gall.Seals.skipσ
