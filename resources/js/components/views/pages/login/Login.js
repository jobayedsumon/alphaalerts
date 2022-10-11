import React from 'react'
import {Link, Navigate} from 'react-router-dom'
import {
    CButton,
    CCard,
    CCardBody,
    CCardGroup,
    CCol,
    CContainer,
    CForm,
    CFormInput, CImage,
    CInputGroup,
    CInputGroupText,
    CRow,
} from '@coreui/react'
import CIcon from '@coreui/icons-react'
import {cilLockLocked, cilUser} from '@coreui/icons'
import axios from "axios";
import {isLoggedIn, login, setUserToken, walletConnect} from "../../../helpers/authHelper";
import {swalError} from "../../../helpers/common";
import {useDispatch} from "react-redux";
import fetchWrapper from "../../../helpers/fetchWrapper";
import logo from "../../../assets/images/logo.png";

const Login = () => {

    const dispatch = useDispatch();

    const walletConnectHandler = (e) => {
        e.preventDefault();
        walletConnect().then(response => {
            if (response && response.user && response.token) {
                fetchWrapper.defaults.headers.common['Authorization'] = 'Bearer ' + response.token;
                dispatch({type: 'set', user: response.user, token: response.token});
            }
        }).catch(error => {
            swalError("Error connecting wallet");
        })
    }

    const handleSubmit = (e) => {
        e.preventDefault()
        const email = e.target.email.value;
        const password = e.target.password.value;
        login(email, password).then(response => {
                if (response && response.user && response.token) {
                    fetchWrapper.defaults.headers.common['Authorization'] = 'Bearer ' + response.token;
                    dispatch({type: 'set', user: response.user, token: response.token});
                }
            }
        ).catch(error => {
                swalError("Error logging in");
            }
        );
    }

    return (
        isLoggedIn() ? <Navigate to="/" replace/> :
            <div className=" min-vh-100 d-flex flex-row align-items-center loginPage">
                <CContainer>

                    <CRow className="justify-content-center align-items-center">

                        <CCol md={6} className="text-center">
                            <CImage src={logo} />
                            <CForm onSubmit={handleSubmit}>
                                <h1 className="text-white text-center">Sign In to your account</h1>
                                <CInputGroup className="mb-3">
                                    <CFormInput type="email" placeholder="Email" name="email"/>
                                </CInputGroup>
                                <CInputGroup className="mb-4">
                                    <CFormInput
                                        type="password"
                                        placeholder="Password"
                                        name="password"
                                    />
                                </CInputGroup>
                                <CRow className="text-center">
                                    <CCol md={12}>
                                        <CButton color="primary" type="submit" className="px-4">
                                            Login
                                        </CButton>
                                    </CCol>
                                </CRow>
                            </CForm>
                        </CCol>
                        <CCol md={2} className="walletButton">
                            <div className="d-flex align-items-center">
                                <h6 className="text-white">OR</h6>
                                <CButton className="mx-3" onClick={walletConnectHandler}>CONNECT WALLET</CButton>
                            </div>

                        </CCol>
                    </CRow>
                </CContainer>
            </div>
    )
}

export default Login
