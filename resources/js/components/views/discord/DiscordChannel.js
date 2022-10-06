import React, {useEffect, useState} from "react";
import {Link, useParams} from "react-router-dom";
import CustomTable from "../../common-components/CustomTable";
import DiscordInfo from "./DiscordInfo";
import fetchWrapper from "../../helpers/fetchWrapper";
import CIcon from "@coreui/icons-react";
import {cilMenu, cilUser} from "@coreui/icons";
import {CCard, CCardBody, CCardHeader} from "@coreui/react";
import moment from "moment";
import {useSelector} from "react-redux";

const DiscordChannel = () => {

    const params = useParams();
    const id = params.id;
    const [messages, setMessages] = useState([]);

    useEffect(() => {

            fetchWrapper.get('/api/discord-messages/'+id)
                .then(response => {
                        const data = response.data;
                        if (data.status === 'success') {
                            setMessages(data.messages);
                        }
                    }
                ).catch(error => {
                setMessages([]);
            });

    }, []);

    return <>

        <DiscordInfo/>

        <CCard>
            <CCardHeader>
                <span className="fs-5">Discord Server Announcements</span>
            </CCardHeader>
            <CCardBody>
                <div className="scroll scroll-pull" data-mobile-height="350" style={{
                    height: '600px',
                    overflowY: 'scroll',
                }}>
                    <div className="messages">
                        {messages.map(message =>
                            <div className="d-flex flex-column mb-3 align-items-start">
                                <div className="d-flex align-items-center">
                                    <div className="fs-1">
                                        {message.author.avatar ? <img alt="Pic" width={40} src={`https://cdn.discordapp.com/avatars/${message.author.id}/${message.author.avatar}.png`}/>
                                            : <CIcon icon={cilUser} size="xl" /> }

                                    </div>
                                    <div className="mx-2">
                                        <Link className="text-decoration-none text-black">{message.author.username}</Link>
                                        <br/>
                                        <small className="text-muted">{
                                           moment(message.timestamp).fromNow()
                                        }</small>
                                    </div>
                                </div>
                                <div className="mt-2 rounded p-2 bg-light text-black fs-6 text-left">
                                    <div dangerouslySetInnerHTML={
                                        {__html: message.content}
                                    }></div>
                                </div>
                            </div>
                        )}
                    </div>
                </div>
            </CCardBody>
        </CCard>



    </>
}

export default DiscordChannel;
