import React, {useEffect, useState} from 'react'

import {Link, useNavigate, useParams} from "react-router-dom";
import {
    CButton,
    CCard,
    CCardBody,
    CCardHeader,
    CCol,
    CForm,
    CFormInput,
    CFormLabel, CFormSelect,
    CInputGroup,
    CRow
} from "@coreui/react";
import fetchWrapper from "../../helpers/fetchWrapper";
import {swalError, swalSuccess} from "../../helpers/common";
import {useDispatch, useSelector} from "react-redux";
import countries from "../../helpers/countries";


const Profile = () => {
    const navigate = useNavigate();
    const dispatch = useDispatch();

    const user = useSelector(state => state.user);

    const handleSubmit = (e) => {
        e.preventDefault();

        const name = e.target.name.value;
        const email = e.target.email.value;
        const country_code = e.target.country_code.value;
        const phone_number = e.target.phone_number.value;

        fetchWrapper.put('/api/profile', {
            name: name,
            email: email,
            country_code: country_code,
            phone_number: phone_number,
        }).then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                swalSuccess("Profile updated successfully");
                dispatch({type: 'set', user: data.user});
                localStorage.setItem('user', JSON.stringify(data.user));
                navigate('/profile');
            } else {
                swalError("Error updating profile");
            }
        }).catch((error) => {
            swalError("Error updating profile");
        });
    }

    return (
        <>
            <CCard>
                <CCardHeader>Manage Profile</CCardHeader>
                <CCardBody>
                    <CForm className="mt-2" onSubmit={handleSubmit}>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Name*</CFormLabel>
                                    <CFormInput name="name" className="col-4" type="text" defaultValue={user.name} required={true} />
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Email*</CFormLabel>
                                    <CFormInput name="email" className="col-4" type="email" defaultValue={user.email} required={true} />
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Country Code*</CFormLabel>
                                    <CFormSelect name="country_code" size="lg" aria-label="Country Code" defaultValue={user.country_code} required={true}>
                                        <option>Select Country</option>
                                        {
                                            countries && countries.map((country, index) =>
                                                <option key={index} value={`+${country.dial_code}`}>{`${country.name} (+${country.dial_code})`}</option>)
                                        }
                                    </CFormSelect>
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mb-3">
                            <CCol md="8">
                                <CInputGroup>
                                    <CFormLabel className="col-3">Phone Number*</CFormLabel>
                                    <CFormInput name="phone_number" className="col-4" type="text" defaultValue={user.phone_number} required={true} />
                                </CInputGroup>
                            </CCol>
                        </CRow>
                        <CRow className="mt-4 mx-2">
                            <CButton type="submit" color="primary" className="col-2">Submit</CButton>
                            <Link to="/#/" className="btn btn-danger col-2 mx-2">Cancel</Link> 
                        </CRow>
                    </CForm>
                </CCardBody>
            </CCard>

        </>
    )
}

export default Profile
